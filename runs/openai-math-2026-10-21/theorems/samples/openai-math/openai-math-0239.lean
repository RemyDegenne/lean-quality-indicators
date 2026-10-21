namespace OAI

noncomputable section

open Set

open scoped Manifold ContDiff

namespace MorseArnold.SphereSymplectic

open MorseArnold.SphereCaps MorseArnold.Geometry

open scoped Manifold ContDiff Topology

open Set Filter

noncomputable section

local instance sphereFormFinrank : Fact (Module.finrank ℝ R3 = 2 + 1) := ⟨by simp [R3]⟩

lemma derivative_alternating {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) (hw : DifferentiableAt ℝ w x)
    (halt : ∀ y u, w y u u = 0) (z u : E) :
    fderiv ℝ w x z u u = 0 := by
  let A : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ u).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u)
  have h := HasFDerivAt.comp (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (G := ℝ)
    x A.hasFDerivAt hw.hasFDerivAt
  have he : (fun _ : E => (0 : ℝ)) =ᶠ[𝓝 x] fun y => A (w y) :=
    Filter.Eventually.of_forall (fun y => (halt y u).symm)
  have hh := (h.congr_of_eventuallyEq he).fderiv
  simp only [fderiv_fun_const] at hh
  exact (congrArg (fun f : E →L[ℝ] ℝ => f z) hh).symm

end
end MorseArnold.SphereSymplectic
end
end OAI
