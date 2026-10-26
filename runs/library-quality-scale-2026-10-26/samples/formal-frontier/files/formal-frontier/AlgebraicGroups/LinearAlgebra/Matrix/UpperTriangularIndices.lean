/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

/-!
# Diagonal and strict coordinates of upper-triangular matrices

For a linearly ordered index type, a weakly ordered pair is either a diagonal
index or a strictly ordered pair. The equivalence below retains the coordinates
explicitly in both directions and does not require a nonempty or finite type.

For a finite index type the cardinality is `card ι + (card ι).choose 2`, using
mathlib's existing count of strictly ordered pairs. The retained-coordinate
predicate `¬ p.2 < p.1` gives the same indexing type without changing coordinates.
No assertion about a coordinate ring or a scheme dimension is made here.

The coordinate-preserving splitting was introduced by Lattice in this
project. The cardinality calculation uses Mathlib's strict-pair count,
without assuming finiteness for the equivalences themselves.

## References

* Bhavik Mehta and Jon Eugster's strict-pair count in Mathlib,
  `Mathlib/Data/Fintype/Prod.lean`,
  `Fintype.card_product_filter_lt` (via `Mathlib/Data/Finset/Prod.lean`),
  and `Mathlib/Data/Fintype/Sum.lean`, `Fintype.card_sum`, for the finite
  cardinality formula. The order-only equivalences are not these results.
-/

public section

set_option warningAsError true

namespace Matrix

variable (ι : Type*) [LinearOrder ι]

/-- Split a weakly upper-triangular coordinate into its diagonal index or its
strictly upper-triangular pair. -/
@[expose]
def upperTriangularIndicesEquiv :
    {p : ι × ι // p.1 ≤ p.2} ≃ ι ⊕ {p : ι × ι // p.1 < p.2} where
  toFun p := if h : p.1.1 = p.1.2 then Sum.inl p.1.1
    else Sum.inr ⟨p.1, lt_of_le_of_ne p.2 h⟩
  invFun := Sum.elim (fun i => ⟨(i, i), le_rfl⟩) (fun p => ⟨p.1, p.2.le⟩)
  left_inv := by
    rintro ⟨⟨i, j⟩, hij⟩
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  right_inv := by
    rintro (i | ⟨⟨i, j⟩, hij⟩)
    · simp
    · simp [ne_of_lt hij]

@[simp]
theorem upperTriangularIndicesEquiv_diagonal (i : ι) :
    upperTriangularIndicesEquiv ι ⟨(i, i), le_rfl⟩ = Sum.inl i := by
  simp [upperTriangularIndicesEquiv]

@[simp]
theorem upperTriangularIndicesEquiv_strict (p : {p : ι × ι // p.1 < p.2}) :
    upperTriangularIndicesEquiv ι ⟨p.1, p.2.le⟩ = Sum.inr p := by
  simp [upperTriangularIndicesEquiv, ne_of_lt p.2]

@[simp]
theorem upperTriangularIndicesEquiv_symm_inl (i : ι) :
    (upperTriangularIndicesEquiv ι).symm (Sum.inl i) = ⟨(i, i), le_rfl⟩ :=
  rfl

@[simp]
theorem upperTriangularIndicesEquiv_symm_inr (p : {p : ι × ι // p.1 < p.2}) :
    (upperTriangularIndicesEquiv ι).symm (Sum.inr p) = ⟨p.1, p.2.le⟩ :=
  rfl

/-- Recombining the two coordinate cases recovers the original pair. -/
@[simp]
theorem upperTriangularIndicesEquiv_coordinates (p : {p : ι × ι // p.1 ≤ p.2}) :
    Sum.elim (fun i => (i, i)) Subtype.val (upperTriangularIndicesEquiv ι p) = p.1 := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  by_cases h : i = j <;> simp [upperTriangularIndicesEquiv, h]

/-- Changing from the retained-coordinate predicate to the weak-order predicate
does not change either coordinate. -/
@[expose]
def upperTriangularRetainedEquiv :
    {p : ι × ι // ¬ p.2 < p.1} ≃ {p : ι × ι // p.1 ≤ p.2} :=
  Equiv.subtypeEquivRight fun _ => not_lt

@[simp]
theorem upperTriangularRetainedEquiv_val (p : {p : ι × ι // ¬ p.2 < p.1}) :
    (upperTriangularRetainedEquiv ι p).1 = p.1 :=
  rfl

@[simp]
theorem upperTriangularRetainedEquiv_symm_val (p : {p : ι × ι // p.1 ≤ p.2}) :
    ((upperTriangularRetainedEquiv ι).symm p).1 = p.1 :=
  rfl

/-- Diagonal/strict coordinates for the complement of the strictly lower
triangular positions. -/
@[expose]
def upperTriangularRetainedIndicesEquiv :
    {p : ι × ι // ¬ p.2 < p.1} ≃ ι ⊕ {p : ι × ι // p.1 < p.2} :=
  (upperTriangularRetainedEquiv ι).trans (upperTriangularIndicesEquiv ι)

@[simp]
theorem upperTriangularRetainedIndicesEquiv_symm_inl_val (i : ι) :
    ((upperTriangularRetainedIndicesEquiv ι).symm (Sum.inl i)).1 = (i, i) :=
  rfl

@[simp]
theorem upperTriangularRetainedIndicesEquiv_symm_inr_val
    (p : {p : ι × ι // p.1 < p.2}) :
    ((upperTriangularRetainedIndicesEquiv ι).symm (Sum.inr p)).1 = p.1 :=
  rfl

/-- Lattice's coordinate-preserving split counts weakly upper-triangular
positions by the diagonal and strict pairs. The finite count reuses Mathlib's
`Fintype.card_product_filter_lt` and `Fintype.card_sum`; the equivalence
itself requires only a linear order. -/
theorem card_upperTriangularIndices [Fintype ι] :
    Fintype.card {p : ι × ι // p.1 ≤ p.2} =
      Fintype.card ι + (Fintype.card ι).choose 2 := by
  calc
    _ = Fintype.card (ι ⊕ {p : ι × ι // p.1 < p.2}) :=
      Fintype.card_congr (upperTriangularIndicesEquiv ι)
    _ = _ := by
      rw [Fintype.card_sum, Fintype.card_subtype, Fintype.card_product_filter_lt]

/-- The equivalent retained-coordinate predicate has the same finite count. -/
theorem card_upperTriangularRetainedIndices [Fintype ι] :
    Fintype.card {p : ι × ι // ¬ p.2 < p.1} =
      Fintype.card ι + (Fintype.card ι).choose 2 := by
  rw [Fintype.card_congr (upperTriangularRetainedEquiv ι), card_upperTriangularIndices]

-- Empty indices require no exceptional choice of a diagonal point.
example [IsEmpty ι] : IsEmpty {p : ι × ι // p.1 ≤ p.2} := inferInstance

example : Fintype.card {p : Fin 0 × Fin 0 // p.1 ≤ p.2} = 0 := by
  simp

example : Fintype.card {p : Fin 1 × Fin 1 // p.1 ≤ p.2} = 1 := by
  simp

example : Fintype.card {p : Fin 3 × Fin 3 // ¬ p.2 < p.1} = 6 := by
  simpa using card_upperTriangularRetainedIndices (Fin 3)

end Matrix
