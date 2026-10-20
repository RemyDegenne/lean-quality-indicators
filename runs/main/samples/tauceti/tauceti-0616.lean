public section

noncomputable section

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder

namespace TauCeti.Probability

variable {p : ℕ} {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}

open Classical in
theorem inverseWishartPDFReal_def (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    inverseWishartPDFReal n S B =
      if (B : Matrix (Fin p) (Fin p) ℝ).PosDef then
        S.det ^ (n / 2) * (B : Matrix (Fin p) (Fin p) ℝ).det ^ (-((n + (p : ℝ) + 1) / 2)) *
            Real.exp (-Matrix.trace (S * (B : Matrix (Fin p) (Fin p) ℝ)⁻¹) / 2) /
          ((2 : ℝ) ^ (n * (p : ℝ) / 2) * multivariateGamma p (n / 2))
      else 0 :=
  (rfl)

end TauCeti.Probability
end
end
