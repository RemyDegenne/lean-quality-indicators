public section

noncomputable section

open Filter

open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups

namespace StronglyContinuousGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The infinitesimal generator of a unitary strongly continuous group as a complex-linear
partially defined map: the complex generator of its forward semigroup. It has the same domain and
values as the existing real generator. -/
def complexGenerator (U : StronglyContinuousGroup H) (hU : U.IsUnitary) : H →ₗ.[ℂ] H :=
  U.toSemigroup.complexGenerator hU.isComplexLinear

end StronglyContinuousGroup
end TauCeti.Semigroups
end
end
