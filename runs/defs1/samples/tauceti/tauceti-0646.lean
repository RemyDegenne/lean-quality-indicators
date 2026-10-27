public section

noncomputable section

open Complex

open scoped Manifold InnerProductSpace

namespace TauCeti.Green

/-- The actual outward-first basis, obtained by complex multiplication from `(1,I)`. -/
def outwardFirstBasis (v : ℂ) (hv : v ≠ 0) : Module.Basis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.map
    ((LinearEquiv.smulOfNeZero ℂ ℂ (-I * v) (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hv) :
      ℂ ≃ₗ[ℂ] ℂ).restrictScalars ℝ)

end TauCeti.Green
end
end
