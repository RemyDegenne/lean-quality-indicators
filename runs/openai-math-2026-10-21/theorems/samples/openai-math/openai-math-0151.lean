namespace OAI

noncomputable section

namespace ForcedComputation.VelocityDetector

open ShearFlows MeasureTheory Set

theorem PlaneC1L2.cylinder {F G : ℝ → Plane → ℝ} {S : Set ℝ}
    (hF : PlaneC1L2 F G S) :
    CylinderC1L2 (fun t x => F t x.1) (fun t x => G t x.1) S := by
  obtain ⟨U, V, hU, hV, hUV⟩ := hF
  refine ⟨fun t => planeCylinderLift (U t), fun t => planeCylinderLift (V t),
    planeCylinderLift.continuous.comp_continuousOn hU,
    planeCylinderLift.continuous.comp_continuousOn hV, ?_⟩
  intro t ht
  obtain ⟨hu, hv, hd⟩ := hUV t ht
  refine ⟨planeCylinderLift_ae (U t) hu, planeCylinderLift_ae (V t) hv, ?_⟩
  exact planeCylinderLift.hasFDerivAt.comp_hasDerivWithinAt t hd

end ForcedComputation.VelocityDetector
end
end OAI
