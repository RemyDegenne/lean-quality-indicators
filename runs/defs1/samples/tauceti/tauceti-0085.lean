public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (M : Type*) [Field M] [Algebra K M] [Algebra.IsAlgebraic K M]

/-- The topology on an algebraic extension `M` of a nonarchimedean local field `K` induced by the
norm of `algebraicExtensionNormedField K M`. -/
@[expose, implicit_reducible]
def algebraicExtensionNormedFieldTopology : TopologicalSpace M :=
  (algebraicExtensionNormedField K M).toUniformSpace.toTopologicalSpace

end TauCeti
end
end
