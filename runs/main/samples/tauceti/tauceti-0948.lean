public section

open Matrix LaurentPolynomial

open scoped ComplexConjugate

namespace TauCeti.KnotTheory

variable {ι : Type*}

variable [Fintype ι] [DecidableEq ι]

theorem det_tristramLevineForm_figureEightSeifertMatrix_ne_zero (ω : Circle)
    (hω : ω ≠ 1) :
    (tristramLevineForm (figureEightSeifertMatrix.map (Int.castRingHom ℝ)) ω).det ≠ 0 := by
  rw [det_tristramLevineForm_int_ne_zero_iff _ ω hω]
  intro h
  have hre := one_le_re_eval₂_alexander_figureEightSeifertMatrix ω
  rw [h, Complex.zero_re] at hre
  norm_num at hre

end TauCeti.KnotTheory
end
