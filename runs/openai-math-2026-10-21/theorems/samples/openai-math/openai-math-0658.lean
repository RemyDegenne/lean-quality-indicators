namespace OAI

namespace Yau.Geometry

open Yau.Jets

noncomputable section

attribute [local instance] clmTopology clmAdd clmModule

lemma principal_jacobian_sum
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (p : QuadParam Coord) (x : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i a : Fin 4) :
    ∑ j, chartPrincipal g i j p x * jacobian (rawQuadratic p) x a j =
      (J.symm (ContinuousLinearMap.inverse (g (rawQuadratic p x)) (ContinuousLinearMap.proj a))) i := by
  have h := congrArg (fun v : Coord ↦ v i)
    (inversePulledForm_covector g p x hp J hJ (ContinuousLinearMap.proj a))
  conv_lhs at h => rw [covector_basis ((ContinuousLinearMap.proj a).comp J.toContinuousLinearMap)]
  simpa [chartPrincipal,jacobian,hJ,map_sum,map_smul,mul_comm] using h

end
end Yau.Geometry
end OAI
