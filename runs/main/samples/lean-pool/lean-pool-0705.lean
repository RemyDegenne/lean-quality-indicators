@[expose] public section

namespace NRR.Geometry

namespace ConvexBody

section Topological

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

theorem exists_mem_interior (K : ConvexBody E) :
    ∃ x : E, x ∈ interior (K : Set E) :=
  K.interior_nonempty

end Topological
end ConvexBody
end NRR.Geometry
end
