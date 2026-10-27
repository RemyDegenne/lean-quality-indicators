/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.GroupTheory.FiniteAbelian.Basic

import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# Scalar indices in finitely generated abelian groups

For a finitely generated abelian group `A`, the index of `n • A` is
`n ^ Module.finrank ℤ A` times the cardinality of the kernel of multiplication by `n`.
Here integer module finrank measures torsion-free rank, not the minimum number of
group generators. Injectivity at this one scalar removes the kernel factor;
no global torsion-freeness assumption is needed. Finite generation is essential:
on the additive group `ℚ`, doubling is bijective and has index one, whereas the
integer module finrank is one and the displayed expression is two.

The formula extends Mathlib's `AddSubgroup.index_range_nsmul`, which already computes
the index for finite free integer modules. The lemma
`AddSubgroup.pow_finrank_mul_natCard_ker_nsmul_eq_pow_finrank` compares the right-hand
sides under that theorem's hypotheses. Mathlib's finite abelian group structure
formalization supplies the free-plus-finite-torsion decomposition relevant to the
extension.

## Limitations

All scalars `n : ℕ`, including zero, are allowed. An infinite quotient has index zero,
and `Nat.card` of an infinite kernel is also zero. Thus the identity does not assert
finiteness of either type at zero. For nonzero scalars, quotient finiteness is already
provided by `AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg`.

For a finite-rank complex lattice, the injective case gives the finite-level
cardinality underlying Milne's I.10, Remark 10.7. The identity for general finitely
generated abelian groups, including finite torsion and the zero scalar, is an
extension, not a statement of that remark. No complex uniformization, lattice-rank
calculation, tensor comparison, inverse limit or Tate-module construction is supplied.

## References

* Mathlib's scalar-index formalization in `Mathlib.GroupTheory.IndexNSmul` and
  finitely generated abelian group structure formalization in
  `Mathlib.GroupTheory.FiniteAbelian.Basic`.
* J. S. Milne, *Abelian Varieties*, Chapter I, §10, Remark 10.7, p. 45:
  the finite-level complex-lattice calculation motivating the application.
-/

@[expose] public section

universe u

namespace AddSubgroup

variable (A : Type u) [AddCommGroup A]

private theorem index_range_nsmul_of_ne_zero [AddGroup.FG A] (n : ℕ) (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := A) n).range.index =
      n ^ Module.finrank ℤ A * Nat.card ((nsmulAddMonoidHom (α := A) n).ker) := by
  let : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let T := Submodule.torsion ℤ A
  let q := T.mkQ.toAddMonoidHom
  let H := (nsmulAddMonoidHom (α := A) n).range
  have hqker : q.ker = T.toAddSubgroup := by
    ext a
    simp [q]
  have hqsurj : Function.Surjective q := T.mkQ_surjective
  have hinj := nsmulAddMonoidHom_injective_of_isTorsionFree (M := A ⧸ T) hn
  -- A nonzero scalar is injective on the torsion-free quotient, so a scalar
  -- multiple is torsion only if the original element is torsion.
  have hmem (a : A) (ha : n • a ∈ T) : a ∈ T := by
    apply (Submodule.Quotient.mk_eq_zero T).mp
    change q a = 0
    apply hinj
    change n • q a = n • 0
    rw [← map_nsmul, nsmul_zero]
    exact (Submodule.Quotient.mk_eq_zero T).mpr ha
  have hrange : H.addSubgroupOf T.toAddSubgroup =
      (nsmulAddMonoidHom (α := T) n).range := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      change n • a = x.val at ha
      refine ⟨⟨a, hmem a (ha ▸ x.property)⟩, ?_⟩
      exact Subtype.ext ha
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, rfl⟩
  have hkerle : (nsmulAddMonoidHom (α := A) n).ker ≤ T.toAddSubgroup := by
    intro a ha
    apply hmem
    rw [show n • a = 0 from ha]
    exact T.zero_mem
  have hker : (nsmulAddMonoidHom (α := T) n).ker =
      ((nsmulAddMonoidHom (α := A) n).ker).addSubgroupOf T.toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
    exact Subtype.ext_iff
  have hcard : Nat.card ((nsmulAddMonoidHom (α := T) n).ker) =
      Nat.card ((nsmulAddMonoidHom (α := A) n).ker) := by
    rw [hker]
    exact Nat.card_congr (addSubgroupOfEquivOfLe hkerle).toEquiv
  have hmap : H.map q = (nsmulAddMonoidHom (α := A ⧸ T) n).range := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨q a, (map_nsmul q n a).symm⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := hqsurj a
      exact ⟨n • b, ⟨b, rfl⟩, map_nsmul q n b⟩
  have hindex : (H ⊔ T.toAddSubgroup).index = n ^ Module.finrank ℤ A := by
    have h := H.index_map q
    rw [hqker, q.range_eq_top_of_surjective hqsurj, index_top, mul_one, hmap] at h
    rw [← h, index_range_nsmul, finrank_quotient_eq_of_le_torsion (le_refl T)]
  let : Finite T := Module.finite_of_fg_torsion T Submodule.torsion_isTorsion
  -- The index tower separates the free quotient from the finite torsion subgroup.
  calc
    H.index = H.relIndex T.toAddSubgroup * (H ⊔ T.toAddSubgroup).index := by
      rw [← relIndex_sup_left T.toAddSubgroup H, relIndex_mul_index le_sup_left]
    _ = n ^ Module.finrank ℤ A * Nat.card ((nsmulAddMonoidHom (α := A) n).ker) := by
      rw [relIndex, hrange]
      rw [show (nsmulAddMonoidHom (α := T) n).range.index =
        Nat.card ((nsmulAddMonoidHom (α := T) n).ker) from index_range]
      rw [hcard, hindex, mul_comm]

/-- In a finitely generated abelian group, the index of multiplication by `n` is
`n` to the integer module finrank times the natural cardinality of its kernel.
This extends the finite free scalar-index formula to groups with finite torsion.
It holds also at zero, with `Nat.card` and index zero for infinite types. -/
theorem index_range_nsmul_eq_mul_natCard_ker [AddGroup.FG A] (n : ℕ) :
    (nsmulAddMonoidHom (α := A) n).range.index =
      n ^ Module.finrank ℤ A * Nat.card ((nsmulAddMonoidHom (α := A) n).ker) := by
  obtain rfl | hn := eq_or_ne n 0
  · have hzero : nsmulAddMonoidHom (α := A) 0 = 0 := by ext; simp
    rw [hzero]
    simp only [AddMonoidHom.range_zero, AddMonoidHom.ker_zero, index_bot, card_top]
    by_cases hA : Finite A
    · let : Finite A := hA
      have hrank : Module.finrank ℤ A = 0 :=
        (isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite).finrank_eq_zero
      simp [hrank]
    · let : Infinite A := not_finite_iff_infinite.mp hA
      simp [Nat.card_eq_zero_of_infinite]
  · exact index_range_nsmul_of_ne_zero A n hn

/-- Injectivity of multiplication by the specified scalar suffices for the scalar-index
formula in a finitely generated abelian group. The group need not be torsion-free,
and the scalar need not be nonzero. -/
theorem index_range_nsmul_of_injective [AddGroup.FG A] (n : ℕ)
    (hinj : Function.Injective (nsmulAddMonoidHom (α := A) n)) :
    (nsmulAddMonoidHom (α := A) n).range.index = n ^ Module.finrank ℤ A := by
  rw [index_range_nsmul_eq_mul_natCard_ker, AddMonoidHom.ker_eq_bot _ hinj]
  simp

/-- For a finite free integer module, the kernel-weighted expression agrees with the
right-hand side of Mathlib's `AddSubgroup.index_range_nsmul` for every scalar.
At zero and positive rank, the kernel is infinite and both sides are zero;
at rank zero, the module and kernel are trivial and both sides are one. -/
theorem pow_finrank_mul_natCard_ker_nsmul_eq_pow_finrank
    [Module.Free ℤ A] [Module.Finite ℤ A] (n : ℕ) :
    n ^ Module.finrank ℤ A * Nat.card ((nsmulAddMonoidHom (α := A) n).ker) =
      n ^ Module.finrank ℤ A := by
  let : AddGroup.FG A := Module.Finite.iff_addGroup_fg.mp inferInstance
  rw [← index_range_nsmul_eq_mul_natCard_ker, index_range_nsmul]

end AddSubgroup
