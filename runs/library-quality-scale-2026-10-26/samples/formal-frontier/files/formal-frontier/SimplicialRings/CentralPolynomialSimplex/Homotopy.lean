/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialRings.CentralPolynomialSimplex
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# The central-polynomial simplicial contraction

The extra polynomial variable is multiplied by a homogeneous-coordinate tail.
The construction works for arbitrary unital rings, including noncommutative rings.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

/-- The sum of homogeneous coordinates at or after the cutoff, including empty tails. -/
def tail (n q : ℕ) : PolyRing R n :=
  ∑ j : Fin (n + 1), if q ≤ j.val then coordinate n j else 0

theorem tail_zero (n : ℕ) : tail (R := R) n 0 = 1 := by
  simp [tail, coordinate_sum]

theorem tail_empty (n : ℕ) (q : ℕ) (hq : n < q) : tail (R := R) n q = 0 := by
  simp [tail, show ∀ j : Fin (n + 1), ¬q ≤ j.val from fun j => by omega]

theorem tail_mem_center (n q : ℕ) :
    tail (R := R) n q ∈ Set.center (PolyRing R n) := by
  unfold tail
  exact Finset.sum_induction _ _ (fun _ _ => Set.add_mem_center)
    (Semigroup.mem_center_iff.mpr (by intro; simp)) (fun j _ => by
      split_ifs <;> [exact coordinate_mem_center n j; exact
        Semigroup.mem_center_iff.mpr (by intro; simp)])

/-- Ordinal substitutions pull a tail back to the inverse image of its cutoff. -/
theorem ordinalMap_tail {m n : ℕ}
    (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (q : ℕ) :
    ordinalMap (R := R) alpha (tail n q) =
      ∑ k : Fin (m + 1),
        if q ≤ (alpha.toOrderHom k).val then coordinate m k else 0 := by
  classical
  simp only [tail, map_sum, apply_ite, map_zero, ordinalMap_coordinate, fiberValue]
  calc
    _ = ∑ j : Fin (n + 1), ∑ k : Fin (m + 1),
        if alpha.toOrderHom k = j ∧ q ≤ j.val then coordinate m k else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : q ≤ j.val <;> simp [hj]
    _ = ∑ k : Fin (m + 1), ∑ j : Fin (n + 1),
        if alpha.toOrderHom k = j ∧ q ≤ j.val then coordinate m k else 0 :=
          Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Every face takes a tail to the tail with the cutoff shifted across its omission. -/
theorem ordinalMap_tail_face (n : ℕ) (i : Fin (n + 2)) (q : ℕ) :
    ordinalMap (R := R) (SimplexCategory.δ i) (tail (n + 1) q) =
      tail n (if i.val < q then q - 1 else q) := by
  rw [ordinalMap_tail]
  simp only [tail]
  apply Finset.sum_congr rfl
  intro k _
  have cutoff : q ≤ ((SimplexCategory.δ i).toOrderHom k).val ↔
      (if i.val < q then q - 1 else q) ≤ k.val := by
    change q ≤ (Fin.succAbove i k).val ↔ _
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega
  simp only [cutoff]

/-- Every degeneracy takes a tail to the tail with the cutoff shifted across its repeat. -/
theorem ordinalMap_tail_degeneracy (n : ℕ) (i : Fin (n + 1)) (q : ℕ) :
    ordinalMap (R := R) (SimplexCategory.σ i) (tail n q) =
      tail (n + 1) (if i.val < q then q + 1 else q) := by
  rw [ordinalMap_tail]
  simp only [tail]
  apply Finset.sum_congr rfl
  intro k _
  have cutoff : q ≤ ((SimplexCategory.σ i).toOrderHom k).val ↔
      (if i.val < q then q + 1 else q) ≤ k.val := by
    change q ≤ (Fin.predAbove i k).val ↔ _
    simp only [Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
      Fin.val_pred, Fin.coe_castPred]
    split_ifs <;> omega
  simp only [cutoff]

@[simp] theorem coefficientMap_tail {S : Type v} [Ring S]
    (phi : R →+* S) (n q : ℕ) :
    coefficientMap phi n (tail (R := R) n q) = tail (R := S) n q := by
  simp only [tail, map_sum, apply_ite, map_zero, coefficientMap_coordinate]

/-- A central coefficient stays central in a central polynomial ring. -/
theorem coefficient_mem_center (n : ℕ) {r : R} (hr : r ∈ Set.center R) :
    coefficient n r ∈ Set.center (PolyRing R n) := by
  apply Semigroup.mem_center_iff.mpr
  intro p
  exact (AddMonoidAlgebra.single_commute (R := R) (M := Fin n →₀ ℕ)
    (m := 0) (r := r) (fun _ => AddCommute.zero_left _) (fun s =>
      (Semigroup.mem_center_iff.mp hr s).symm) p).eq.symm

/-- The extra polynomial variable embedded as a coefficient is central. -/
theorem polynomialX_mem_center (n : ℕ) :
    coefficient (R := Polynomial R) n Polynomial.X ∈
      Set.center (PolyRing (Polynomial R) n) := by
  apply coefficient_mem_center
  apply Semigroup.mem_center_iff.mpr
  intro p
  exact (Polynomial.commute_X p).eq.symm

/-- Evaluation of the coefficient polynomial at `x` times a tail. -/
def homotopyCoefficient (n : ℕ) (i : Fin (n + 1)) :
    Polynomial R →+* PolyRing (Polynomial R) (n + 1) :=
  Polynomial.eval₂RingHom'
    ((coefficient (R := Polynomial R) (n + 1)).comp Polynomial.C)
    (coefficient (R := Polynomial R) (n + 1) Polynomial.X * tail (n + 1) (i.val + 1))
    (fun r => by
      have hc : coefficient (R := Polynomial R) (n + 1) Polynomial.X *
          tail (R := Polynomial R) (n + 1) (i.val + 1) ∈
          Set.center (PolyRing (Polynomial R) (n + 1)) :=
        Set.mul_mem_center (polynomialX_mem_center (R := R) (n + 1))
          (tail_mem_center (R := Polynomial R) (n + 1) (i.val + 1))
      exact Semigroup.mem_center_iff.mp hc _)

@[simp] theorem homotopyCoefficient_C (n : ℕ) (i : Fin (n + 1)) (r : R) :
    homotopyCoefficient n i (Polynomial.C r) =
      coefficient (R := Polynomial R) (n + 1) (Polynomial.C r) := by
  simp [homotopyCoefficient]

@[simp] theorem homotopyCoefficient_X (n : ℕ) (i : Fin (n + 1)) :
    homotopyCoefficient (R := R) n i Polynomial.X =
      coefficient (R := Polynomial R) (n + 1) Polynomial.X *
        tail (R := Polynomial R) (n + 1) (i.val + 1) := by
  simp [homotopyCoefficient]

/-- The degree-raising ring map at index `i` of the simplicial contraction. -/
def homotopyMap (n : ℕ) (i : Fin (n + 1)) :
    PolyRing (Polynomial R) n →+* PolyRing (Polynomial R) (n + 1) :=
  substitute n (homotopyCoefficient n i) (fun j =>
    ⟨fiberValue (SimplexCategory.σ i) j.succ, fiber_mem_center _ _⟩)

@[simp] theorem homotopyMap_coefficient (n : ℕ) (i : Fin (n + 1))
    (p : Polynomial R) :
    homotopyMap n i (coefficient n p) = homotopyCoefficient n i p := by
  exact substitute_coefficient ..

@[simp] theorem homotopyMap_generator (n : ℕ) (i : Fin (n + 1))
    (j : Fin n) :
    homotopyMap (R := R) n i (generator n j) =
      fiberValue (R := Polynomial R) (SimplexCategory.σ i) j.succ := by
  exact substitute_generator ..

@[simp] theorem homotopyMap_coordinate (n : ℕ) (i : Fin (n + 1))
    (j : Fin (n + 1)) :
    homotopyMap (R := R) n i (coordinate n j) =
      ordinalMap (R := Polynomial R) (SimplexCategory.σ i) (coordinate n j) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [coordinate_zero, map_sub, map_sum]
  · simp

theorem polynomialPolyRing_hom_ext {B : Type v} [Ring B] {n : ℕ}
    {f g : PolyRing (Polynomial R) n →+* B}
    (hconst : ∀ r : R, f (coefficient n (Polynomial.C r)) =
      g (coefficient n (Polynomial.C r)))
    (hx : f (coefficient n Polynomial.X) = g (coefficient n Polynomial.X))
    (hcoord : ∀ j : Fin n, f (generator n j) = g (generator n j)) : f = g := by
  apply hom_ext
  · intro p
    have h : f.comp (coefficient n) = g.comp (coefficient n) :=
      Polynomial.ringHom_ext hconst hx
    exact RingHom.congr_fun h p
  · exact hcoord

theorem homotopyMap_ordinal_generator (n : ℕ) (i : Fin (n + 1))
    {m : ℕ} (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk (n + 1))
    (j : Fin n) :
    ((ordinalMap (R := Polynomial R) alpha).comp (homotopyMap n i)) (generator n j) =
      ordinalMap (R := Polynomial R) (alpha ≫ SimplexCategory.σ i) (generator n j) := by
  have h := ordinalMap_comp (R := Polynomial R) alpha (SimplexCategory.σ i)
  simpa only [RingHom.comp_apply, homotopyMap_generator, ordinalMap_generator] using
    congrArg (fun f : PolyRing (Polynomial R) n →+* PolyRing (Polynomial R) m =>
      f (generator n j)) h

theorem ordinal_homotopyMap_generator (n : ℕ) (i : Fin (n + 1))
    {l : ℕ} (alpha : SimplexCategory.mk n ⟶ SimplexCategory.mk l)
    (j : Fin l) :
    ((homotopyMap n i).comp (ordinalMap (R := Polynomial R) alpha)) (generator l j) =
      ordinalMap (R := Polynomial R) (SimplexCategory.σ i ≫ alpha) (generator l j) := by
  simp only [RingHom.comp_apply, ordinalMap_generator]
  calc
    homotopyMap n i (fiberValue alpha j.succ) =
        ordinalMap (R := Polynomial R) (SimplexCategory.σ i)
          (fiberValue alpha j.succ) := by
          simp only [fiberValue, map_sum, apply_ite, map_zero,
            homotopyMap_coordinate, ordinalMap_coordinate]
    _ = _ := ordinalMap_fiberValue (SimplexCategory.σ i) alpha j.succ

@[simp] theorem homotopyMap_C (n : ℕ) (i : Fin (n + 1)) (r : R) :
    homotopyMap n i (coefficient n (Polynomial.C r)) =
      coefficient (R := Polynomial R) (n + 1) (Polynomial.C r) := by
  simp

@[simp] theorem homotopyMap_X (n : ℕ) (i : Fin (n + 1)) :
    homotopyMap (R := R) n i (coefficient n Polynomial.X) =
      coefficient (R := Polynomial R) (n + 1) Polynomial.X *
        tail (R := Polynomial R) (n + 1) (i.val + 1) := by
  simp

theorem homotopyMap_face_zero (n : ℕ) :
    (ordinalMap (R := Polynomial R) (SimplexCategory.δ (0 : Fin (n + 2)))).comp
      (homotopyMap n (0 : Fin (n + 1))) = RingHom.id _ := by
  apply polynomialPolyRing_hom_ext
  · intro r; simp
  · simp [RingHom.comp_apply, ordinalMap_tail_face, tail_zero]
  · intro j
    rw [homotopyMap_ordinal_generator]
    have h : SimplexCategory.δ (0 : Fin (n + 2)) ≫
        SimplexCategory.σ (0 : Fin (n + 1)) = 𝟙 _ :=
      SimplexCategory.δ_comp_σ_self (i := (0 : Fin (n + 1)))
    rw [h, ordinalMap_id]

theorem homotopyMap_face_last (n : ℕ) :
    (ordinalMap (R := Polynomial R) (SimplexCategory.δ (Fin.last (n + 1)))).comp
      (homotopyMap n (Fin.last n)) =
      (coefficientMap (Polynomial.C (R := R)) n).comp
        (coefficientMap (Polynomial.constantCoeff (R := R)) n) := by
  apply polynomialPolyRing_hom_ext
  · intro r; simp [Polynomial.constantCoeff]
  · simp [RingHom.comp_apply, ordinalMap_tail_face,
      tail_empty, Polynomial.constantCoeff]
  · intro j
    rw [homotopyMap_ordinal_generator]
    have h := SimplexCategory.δ_comp_σ_succ (i := Fin.last n)
    simp only [Fin.succ_last] at h
    rw [h, ordinalMap_id]
    simp

theorem homotopyMap_face_before {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
    (ordinalMap (R := Polynomial R) (SimplexCategory.δ i.castSucc)).comp
      (homotopyMap (n + 1) j.succ) =
    (homotopyMap n j).comp (ordinalMap (SimplexCategory.δ i)) := by
  apply polynomialPolyRing_hom_ext
  · intro r; simp
  · simp only [RingHom.comp_apply, homotopyMap_X, map_mul, ordinalMap_coefficient,
      ordinalMap_tail_face]
    have hcut :
        (if (i.castSucc).val < (j.succ).val + 1 then (j.succ).val + 1 - 1
          else (j.succ).val + 1) = j.val + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hle : i.val ≤ j.val := by
        simpa only [Fin.val_castSucc] using (Fin.le_iff_val_le_val.mp hij)
      have hcutpos : i.val < j.val + 1 + 1 := by omega
      rw [ite_eq_left hcutpos]
      omega
    rw [hcut]
  · intro k
    rw [homotopyMap_ordinal_generator, ordinal_homotopyMap_generator,
      SimplexCategory.δ_comp_σ_of_le hij]

theorem homotopyMap_face_middle {n : ℕ} (j : Fin (n + 1)) :
    (ordinalMap (R := Polynomial R) (SimplexCategory.δ j.castSucc.succ)).comp
      (homotopyMap (n + 1) j.succ) =
    (ordinalMap (R := Polynomial R) (SimplexCategory.δ j.castSucc.succ)).comp
      (homotopyMap (n + 1) j.castSucc) := by
  apply polynomialPolyRing_hom_ext
  · intro r; simp
  · simp only [RingHom.comp_apply, homotopyMap_X, map_mul, ordinalMap_coefficient,
      ordinalMap_tail_face]
    have leftCut : (if (j.castSucc.succ).val < (j.succ).val + 1 then
        (j.succ).val + 1 - 1 else (j.succ).val + 1) = j.val + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
    have rightCut : (if (j.castSucc.succ).val < (j.castSucc).val + 1 then
        (j.castSucc).val + 1 - 1 else (j.castSucc).val + 1) = j.val + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega
    rw [leftCut, rightCut]
  · intro k
    rw [homotopyMap_ordinal_generator, homotopyMap_ordinal_generator]
    have leftId : SimplexCategory.δ j.castSucc.succ ≫
        SimplexCategory.σ j.succ = 𝟙 _ := by
      simpa only [Fin.castSucc_succ] using
        (SimplexCategory.δ_comp_σ_self (i := j.succ))
    have rightId : SimplexCategory.δ j.castSucc.succ ≫
        SimplexCategory.σ j.castSucc = 𝟙 _ :=
      SimplexCategory.δ_comp_σ_succ (i := j.castSucc)
    rw [leftId, rightId]

theorem homotopyMap_face_after {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
    (ordinalMap (R := Polynomial R) (SimplexCategory.δ i.succ)).comp
      (homotopyMap (n + 1) j.castSucc) =
    (homotopyMap n j).comp (ordinalMap (SimplexCategory.δ i)) := by
  apply polynomialPolyRing_hom_ext
  · intro r; simp
  · simp only [RingHom.comp_apply, homotopyMap_X, map_mul, ordinalMap_coefficient,
      ordinalMap_tail_face]
    have hcut : (if i.succ.val < j.castSucc.val + 1 then j.castSucc.val + 1 - 1
        else j.castSucc.val + 1) = j.val + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hlt : j.val < i.val := by
        simpa only [Fin.val_castSucc] using (Fin.lt_def.mp hji)
      split_ifs <;> omega
    rw [hcut]
  · intro k
    rw [homotopyMap_ordinal_generator, ordinal_homotopyMap_generator,
      SimplexCategory.δ_comp_σ_of_gt hji]

theorem homotopyMap_degeneracy_before {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    (ordinalMap (R := Polynomial R) (SimplexCategory.σ i.castSucc)).comp
      (homotopyMap n j) =
    (homotopyMap (n + 1) j.succ).comp (ordinalMap (SimplexCategory.σ i)) := by
  apply polynomialPolyRing_hom_ext
  · intro r; simp
  · simp only [RingHom.comp_apply, homotopyMap_X, map_mul, ordinalMap_coefficient,
      ordinalMap_tail_degeneracy]
    have hcut : (if i.castSucc.val < j.val + 1 then j.val + 1 + 1 else j.val + 1) =
        j.succ.val + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hle : i.val ≤ j.val := Fin.le_iff_val_le_val.mp hij
      split_ifs <;> omega
    rw [hcut]
  · intro k
    rw [homotopyMap_ordinal_generator, ordinal_homotopyMap_generator,
      SimplexCategory.σ_comp_σ hij]

theorem homotopyMap_degeneracy_after {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    (ordinalMap (R := Polynomial R) (SimplexCategory.σ i.succ)).comp
      (homotopyMap n j) =
    (homotopyMap (n + 1) j.castSucc).comp (ordinalMap (SimplexCategory.σ i)) := by
  apply polynomialPolyRing_hom_ext
  · intro r; simp
  · simp only [RingHom.comp_apply, homotopyMap_X, map_mul, ordinalMap_coefficient,
      ordinalMap_tail_degeneracy]
    have hcut : (if i.succ.val < j.val + 1 then j.val + 1 + 1 else j.val + 1) =
        j.castSucc.val + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hle : j.val ≤ i.val := Fin.le_iff_val_le_val.mp hji
      split_ifs <;> omega
    rw [hcut]
  · intro k
    rw [homotopyMap_ordinal_generator, ordinal_homotopyMap_generator,
      ← SimplexCategory.σ_comp_σ hji]

/-- The native simplicial homotopy, with its map family and seven identity laws, from evaluation-then-inclusion to
the identity, valid over every unital ring. -/
def contraction (A : RingCat.{u}) : CategoryTheory.SimplicialObject.Homotopy
    (evalAtZero A ≫ constantInclusion A)
    (𝟙 (simplex (polynomialFunctor.obj A))) where
  h i := RingCat.ofHom (homotopyMap (R := A) _ i)
  h_zero_comp_δ_zero n := by
    apply RingCat.hom_ext
    exact homotopyMap_face_zero (R := A) n
  h_last_comp_δ_last n := by
    apply RingCat.hom_ext
    exact homotopyMap_face_last (R := A) n
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply RingCat.hom_ext
    exact homotopyMap_face_before (R := A) i j hij
  h_succ_comp_δ_castSucc_succ j := by
    apply RingCat.hom_ext
    exact homotopyMap_face_middle (R := A) j
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply RingCat.hom_ext
    exact homotopyMap_face_after (R := A) i j hji
  h_comp_σ_castSucc_of_le i j hij := by
    apply RingCat.hom_ext
    exact homotopyMap_degeneracy_before (R := A) i j hij
  h_comp_σ_succ_of_lt i j hji := by
    apply RingCat.hom_ext
    exact homotopyMap_degeneracy_after (R := A) i j hji

/-- The degree-raising maps commute with every coefficient ring homomorphism. -/
theorem homotopyMap_natural {S : Type v} [Ring S] (phi : R →+* S)
    (n : ℕ) (i : Fin (n + 1)) :
    (coefficientMap (Polynomial.mapRingHom phi) (n + 1)).comp
      (homotopyMap (R := R) n i) =
    (homotopyMap (R := S) n i).comp
      (coefficientMap (Polynomial.mapRingHom phi) n) := by
  apply polynomialPolyRing_hom_ext
  · intro r
    simp [RingHom.comp_apply]
  · simp [RingHom.comp_apply, coefficientMap_tail]
  · intro j
    simp only [RingHom.comp_apply, homotopyMap_generator, coefficientMap_generator]
    simp only [fiberValue, map_sum, apply_ite, map_zero, coefficientMap_coordinate]

end
end CentralPolynomialSimplex
