/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.AdditiveEuler
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Finite-support Euler sums and native cochain shifts

Signed sums over any two intervals agree when each contains the support of the
summand. Translation of signed sums has no support or additivity requirement.
For native cochain complexes, both the terms and homology of `K⟦n⟧` are those
of `K` in degree `i + n`; the latter comparison uses mathlib's shift isomorphism.
All statements hold for additive-commutative-group values, including torsion.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators ZeroObject

namespace CategoryTheory.AdditiveEuler

universe u v w

variable {Γ : Type w} [AddCommGroup Γ]

/-- Finite signed sums are independent of two possibly empty, nonnested support
intervals. If either interval is empty, its support assumption makes `f` zero. -/
theorem signed_sum_eq_of_support (f : ℤ → Γ) (a b c d : ℤ)
    (hab : ∀ i, i < a ∨ b < i → f i = 0)
    (hcd : ∀ i, i < c ∨ d < i → f i = 0) :
    (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • f i) =
      ∑ i ∈ Finset.Icc c d, (Int.negOnePow i : ℤ) • f i := by
  let s := Finset.Icc a b
  let t := Finset.Icc c d
  calc
    (∑ i ∈ s, (Int.negOnePow i : ℤ) • f i) =
        ∑ i ∈ s ∪ t, (Int.negOnePow i : ℤ) • f i := by
      apply Finset.sum_subset Finset.subset_union_left
      intro i _ hi
      rw [hab i (by simpa only [s, Finset.mem_Icc, not_and_or, not_le] using hi), smul_zero]
    _ = ∑ i ∈ t, (Int.negOnePow i : ℤ) • f i := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro i _ hi
      rw [hcd i (by simpa only [t, Finset.mem_Icc, not_and_or, not_le] using hi), smul_zero]

/-- Translate a signed interval sum by any integer, including empty intervals. -/
theorem signed_sum_translate (f : ℤ → Γ) (a b n : ℤ) :
    (∑ i ∈ Finset.Icc (a - n) (b - n), (Int.negOnePow i : ℤ) • f (i + n)) =
      (Int.negOnePow n : ℤ) •
        ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • f j := by
  have htranslate :
      (∑ i ∈ Finset.Icc (a - n) (b - n), (Int.negOnePow i : ℤ) • f (i + n)) =
        ∑ j ∈ Finset.Icc a b, (Int.negOnePow (j - n) : ℤ) • f j := by
    apply Finset.sum_bij (fun i _ => i + n)
    · intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    · intro i _ j _ hij
      omega
    · intro j hj
      refine ⟨j - n, ?_, by omega⟩
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro i _
      rw [show i + n - n = i by omega]
  rw [htranslate, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Int.negOnePow_sub, mul_comm, Units.val_mul, mul_zsmul]

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (μ : C → Γ)
variable (hμ : ∀ S : ShortComplex C, S.ShortExact → μ S.X₂ = μ S.X₁ + μ S.X₃)

include hμ

/-- A termwise `IsZero` support bound makes finite Euler sums independent of
the chosen interval, for either chain or cochain complex shapes. -/
theorem term_sum_eq_of_support {c : ComplexShape ℤ} (K : HomologicalComplex C c)
    (a b c' d : ℤ)
    (hab : ∀ i, i < a ∨ b < i → IsZero (K.X i))
    (hcd : ∀ i, i < c' ∨ d < i → IsZero (K.X i)) :
    (∑ i ∈ Finset.Icc a b, (Int.negOnePow i : ℤ) • μ (K.X i)) =
      ∑ i ∈ Finset.Icc c' d, (Int.negOnePow i : ℤ) • μ (K.X i) :=
  signed_sum_eq_of_support (fun i => μ (K.X i)) a b c' d
    (fun i hi => invariant_of_isZero μ hμ (hab i hi))
    (fun i hi => invariant_of_isZero μ hμ (hcd i hi))

omit hμ

/-- Native cochain shifting sends an `IsZero` term bound `[a, b]` to
`[a - n, b - n]`, with no Euler-invariant assumption. -/
theorem cochain_shift_term_support (K : CochainComplex C ℤ) (a b n : ℤ)
    (hK : ∀ j, j < a ∨ b < j → IsZero (K.X j)) :
    ∀ i, i < a - n ∨ b - n < i → IsZero ((K⟦n⟧).X i) := by
  intro i hi
  rw [CochainComplex.shiftFunctor_obj_X']
  exact hK (i + n) (by omega)

/-- Term Euler sums of the actual cochain shift translate without support
bounds or short-exact-sequence additivity. -/
theorem cochain_shift_term_sum (K : CochainComplex C ℤ) (a b n : ℤ) :
    (∑ i ∈ Finset.Icc (a - n) (b - n),
      (Int.negOnePow i : ℤ) • μ ((K⟦n⟧).X i)) =
      (Int.negOnePow n : ℤ) •
        ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.X j) := by
  simpa only [CochainComplex.shiftFunctor_obj_X'] using
    signed_sum_translate (fun j => μ (K.X j)) a b n

/-- Native homology shift comparison, with target degree `i + n`. -/
def cochain_shift_homology_iso (K : CochainComplex C ℤ) (n i : ℤ) :
    (K⟦n⟧).homology i ≅ K.homology (i + n) :=
  (CochainComplex.ShiftSequence.shiftIso C n i (i + n) (by omega)).app K

include hμ

/-- Homology Euler sums translate via the actual native homology shift
isomorphism. No termwise support is needed. -/
theorem cochain_shift_homology_sum (K : CochainComplex C ℤ) (a b n : ℤ) :
    (∑ i ∈ Finset.Icc (a - n) (b - n),
      (Int.negOnePow i : ℤ) • μ ((K⟦n⟧).homology i)) =
      (Int.negOnePow n : ℤ) •
        ∑ j ∈ Finset.Icc a b, (Int.negOnePow j : ℤ) • μ (K.homology j) := by
  calc
    (∑ i ∈ Finset.Icc (a - n) (b - n),
        (Int.negOnePow i : ℤ) • μ ((K⟦n⟧).homology i)) =
        ∑ i ∈ Finset.Icc (a - n) (b - n),
          (Int.negOnePow i : ℤ) • μ (K.homology (i + n)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [invariant_iso μ hμ (cochain_shift_homology_iso K n i)]
    _ = _ := signed_sum_translate (fun j => μ (K.homology j)) a b n

end CategoryTheory.AdditiveEuler
