public section

open CategoryTheory

open scoped DirectSum

namespace TopRep

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{max v w} R G)

/-- The integer homogeneous-piece family of the total resolution, zero in negative degrees. -/
noncomputable def gradedResolutionPiece : ℤ → Submodule R X.gradedResolutionModule :=
  (resolutionModuleComplex X).directSumPiece

end TopRep
end
