@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace PolygonalCircle

variable (J : PolygonalCircle)

theorem incomingRay_mem_closure_vertexSectors (i : ZMod J.n) {r radius : ℝ}
    (hr : 0 < r) (hradius : radius ∈ Set.Icc 0 r) :
    J.vertex i + planeComplexEquiv.symm
        ((radius : ℂ) * (J.incomingRayDirection i : ℂ)) ∈
          closure (J.vertexForwardSector i r) ∩ closure (J.vertexBackwardSector i r) := by
  constructor
  · apply image_closure_subset_closure_image (by fun_prop)
    exact ⟨_, targetRadialRay_mem_closure_openAngularSector _ _ hr hradius, rfl⟩
  · apply image_closure_subset_closure_image (by fun_prop)
    exact ⟨_, sourceRadialRay_mem_closure_openAngularSector _ _ hr hradius, rfl⟩

end PolygonalCircle
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
