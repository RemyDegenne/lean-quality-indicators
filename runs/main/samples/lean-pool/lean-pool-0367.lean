@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex

namespace PolygonCell

@[simp]
theorem rotateHomeomorph_apply_val {n m : ℕ} (h : n = m) (k : ℕ)
    (z : PolygonCell n) :
    (rotateHomeomorph h k z).val = (rotationUnit n k : ℂ) * z.val :=
  by
    subst m
    rfl

end PolygonCell
end LeanEval.Topology.ClassificationOfSurfaces
end
