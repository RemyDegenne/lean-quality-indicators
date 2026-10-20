namespace P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

noncomputable section

universe u

open PowerSeries MvFormalGroup MvFormalGroup.ArtinHasse

namespace LambdaGhost

open PowerSeries

section Lambda

open MvFormalGroup.BigWittLaw

variable {A : Type*} [CommRing A]

variable (n : ℕ)

theorem coeff_gh_frobSeries {n : ℕ} (hn : 0 < n) (m : ℕ) :
    coeff m (gh (frobSeries n)) = coeff (n * m) (gh genSeries) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [mul_zero, coeff_zero_gh, coeff_zero_gh]
  have hm0 : m ≠ 0 := by omega
  have hP1 : constantCoeff (∏ k ∈ Finset.range (n * m), frobFactor n k) = 1 := by
    rw [map_prod]; exact Finset.prod_eq_one fun k _ => constantCoeff_frobFactor n k
  rw [coeff_gh_eq_of_coeff_eq (constantCoeff_frobSeries n) hP1 m
      (fun j hj => coeff_frobSeries_eq_coeff_prod hn hj) m le_rfl,
    gh_prod _ _ (fun k _ => constantCoeff_frobFactor n k), map_sum,
    coeff_gh_genSeries (n * m) (Nat.mul_ne_zero hn.ne' hm0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hdpos : 0 < Nat.gcd (k + 1) n := Nat.gcd_pos_of_pos_right _ hn
  have he0 : (k + 1) / Nat.gcd (k + 1) n ≠ 0 := by
    have := Nat.div_mul_cancel (Nat.gcd_dvd_left (k + 1) n)
    intro h; rw [h, zero_mul] at this; omega
  rw [frobFactor, gh_pow (constantCoeff_geomSeries _ _), map_nsmul, coeff_gh_geomSeries _ he0, nsmul_eq_mul]
  exact frob_term_eq (wittCoord k) hn k m hm0

end Lambda
end LambdaGhost
end
end P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam
