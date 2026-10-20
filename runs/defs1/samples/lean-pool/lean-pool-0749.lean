@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace PolygonalCircle

variable (J : PolygonalCircle)

/-- The linear functional whose zero set is parallel to the vector from `p` to `q`. -/
noncomputable def edgeNormalLinear (p q : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun x := (q - p) 0 * x 1 - (q - p) 1 * x 0
  map_add' := by
    intro x y
    simp only [PiLp.add_apply]
    ring
  map_smul' := by
    intro c x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end PolygonalCircle
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
