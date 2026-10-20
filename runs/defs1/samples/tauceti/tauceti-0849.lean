public section

open CategoryTheory

namespace TauCeti

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

attribute [local instance 10000] Classical.decRel

variable (R : Type v) [CommRing R] [TopologicalSpace R]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G)
  (A : SmoothDiscreteTopRep.{v, u, max u v w} R U.toSubgroup)

local instance : U.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient

/-- Smooth discrete induction and algebraic coinduction agree for an open subgroup, through
Mathlib's finite-index comparison. -/
noncomputable def algebraicIndCoindIso :
    algebraicIndAsSmooth.{u, v, w} R G U A ≅ algebraicCoindAsSmooth R G U A :=
  (toSmoothDiscrete R G).mapIso (discreteIndCoindIso.{u, v, w} R G U A)

end TauCeti
end
