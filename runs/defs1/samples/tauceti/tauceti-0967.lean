public section

noncomputable section

open Metric Module

open scoped Manifold ContDiff TauCeti.LinearIsometryEquivOperatorNorm
  TauCeti.DiffeomorphWeakWhitney TauCeti.RiemannianIsometryWeakWhitney

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n k : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)]

local instance : ProperSpace E := FiniteDimensional.proper ℝ E

namespace LinearIsometryEquiv

/-- The full isometry group of the round unit sphere is homeomorphically isomorphic to the
ambient orthogonal group, including the two-point sphere. -/
def unitSphereIsomContinuousMulEquiv :
    (E ≃ₗᵢ[ℝ] E) ≃ₜ* TauCeti.Isom (𝓡 n) (sphere (0 : E) 1) where
  toMulEquiv := unitSphereIsomMulEquiv
  continuous_toFun := by
    rw [MulEquiv.toFun_eq_coe]
    exact (continuous_unitSphereRiemannianIsometry (E := E) (F := E) (n := n) (k := n)).congr
      fun e => ((unitSphereIsomMulEquiv_apply e).trans (unitSphereIsomHom_apply e)).symm
  continuous_invFun := by
    rw [MulEquiv.invFun_eq_symm]
    exact (TauCeti.RiemannianIsometry.continuous_toLinearIsometryEquiv
      (E := E) (F := E) (n := n) (k := n)).congr
        fun Φ => (unitSphereIsomMulEquiv_symm_apply Φ).symm

end LinearIsometryEquiv
end
end
