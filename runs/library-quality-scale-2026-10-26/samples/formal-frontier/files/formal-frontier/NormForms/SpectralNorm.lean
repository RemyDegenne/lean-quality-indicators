/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# The field norm and the spectral norm

For a finite field extension of a complete nonarchimedean normed field, the absolute
value of the algebraic norm is the spectral norm raised to the extension degree.
No norm or topology on the extension field is needed. The base norm may be trivial,
and the extension need not be separable.

The nonarchimedean hypothesis concerns Mathlib's minimal-polynomial root bound
`spectralNorm`: over an archimedean base this bound need not be power-multiplicative.

## References

* I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, second edition,
  Chapter II, §2, norm formulas for finite extensions of complete valued fields.
* Mathlib's spectral-norm formalization by María Inés de Frutos-Fernández, following
  S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §§3.1–3.2.
  The algebraic norm, simple-extension power basis and tower-degree APIs are also
  supplied by Mathlib.
-/

@[expose] public section

universe u v

private theorem spectralNorm_eq_one_of_forall_norm_eq_one
    {K : Type u} {L : Type v} [NormedField K] [Field L] [Algebra K L]
    (hK : ∀ y : K, y ≠ 0 → ‖y‖ = 1) {x : L} (hx : x ≠ 0) (hi : IsIntegral K x) :
    spectralNorm K L x = 1 := by
  change spectralValue (minpoly K x) = 1
  apply le_antisymm
  · apply (spectralValue_le_one_iff (minpoly.monic hi)).2
    intro n
    by_cases h : (minpoly K x).coeff n = 0
    · simp [h]
    · exact le_of_eq (hK _ h)
  · calc
      1 = spectralValueTerms (minpoly K x) 0 := by
        rw [spectralValueTerms_of_lt_natDegree _ (minpoly.natDegree_pos hi),
          hK _ (minpoly.coeff_zero_ne_zero hi hx), Real.one_rpow]
      _ ≤ spectralValue (minpoly K x) :=
        le_ciSup (spectralValueTerms_bddAbove _) 0

open IntermediateField

namespace Algebra

variable {K : Type u} {L : Type v} [NormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- In a finite extension of a complete nonarchimedean normed field, the norm of the
algebraic field norm is the spectral norm to the extension degree. This includes
trivially normed bases and inseparable extensions. It is the exactly extending
absolute-value formula underlying the normalized-valuation norm formula in
Fesenko–Vostokov, *Local Fields and Their Extensions*, Chapter II, §2. -/
theorem norm_norm_eq_spectralNorm_pow_finrank (x : L) :
    ‖Algebra.norm K x‖ = spectralNorm K L x ^ Module.finrank K L := by
  by_cases hx : x = 0
  · subst x
    rw [Algebra.norm_zero, _root_.norm_zero, spectralNorm_zero,
      zero_pow (Module.finrank_pos.ne' : Module.finrank K L ≠ 0)]
  have hi : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  by_cases hK : ∃ y : K, y ≠ 0 ∧ ‖y‖ ≠ 1
  · -- This local class preserves the given base norm and uniformity.
    let := NontriviallyNormedField.ofNormNeOne hK
    have hd : (minpoly K x).natDegree ≠ 0 := (minpoly.natDegree_pos hi).ne'
    have hnorm : ‖Algebra.norm K (IntermediateField.AdjoinSimple.gen K x)‖ =
        ‖(minpoly K x).coeff 0‖ := by
      have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
        (IntermediateField.adjoin.powerBasis hi)
      rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h
      rw [h, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [Algebra.norm_eq_norm_adjoin K x, norm_pow, hnorm,
      spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow]
    -- The tower degree is deg(minpoly) * [L : K(x)], including inseparable degrees.
    rw [← Module.finrank_mul_finrank K K⟮x⟯ L, IntermediateField.adjoin.finrank hi, pow_mul]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    have hd' : ((minpoly K x).natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
    rw [one_div, inv_mul_cancel₀ hd', Real.rpow_one]
  · have htriv : ∀ y : K, y ≠ 0 → ‖y‖ = 1 := by
      intro y hy
      by_contra hnorm
      exact hK ⟨y, hy, hnorm⟩
    rw [htriv _ (Algebra.norm_ne_zero_iff.mpr hx),
      spectralNorm_eq_one_of_forall_norm_eq_one htriv hx hi, one_pow]

end Algebra
