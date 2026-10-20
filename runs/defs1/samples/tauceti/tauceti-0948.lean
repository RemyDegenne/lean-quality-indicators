public section

namespace TauCeti

section Bundled

open CategoryTheory

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance instContinuousSMulOfSmoothDiscreteCoind
    {R : Type u} [Ring R] [TopologicalSpace R] {G : Type v} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (A : SmoothDiscreteTopRep.{u, v, w} R G) :
    ContinuousSMul G A.obj.V := A.property.continuousSMul

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G)

/-- The locally constant coinduced module, bundled as a discrete representation of `G`. -/
noncomputable abbrev coindDiscreteRep (A : DiscreteRep.{u, v, w} R U) :
    DiscreteRep.{u, v, max v w} R G where
  V := DiscreteCoind G U A.V
  smulCommClass := DiscreteCoind.instSMulCommClass
  continuousSMulRing := DiscreteCoind.instContinuousSMulScalar

end Bundled
end TauCeti
end
