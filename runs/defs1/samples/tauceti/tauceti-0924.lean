public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (M : Type*) [Field M] [Algebra K M] [Algebra.IsAlgebraic K M]

/-- The valuative relation on an algebraic extension `M` of a nonarchimedean local field `K` defined
by the norm of `algebraicExtensionNormedField K M`: `x ≤ᵥ y` exactly when `‖x‖ ≤ ‖y‖`. -/
@[expose, implicit_reducible]
def algebraicExtensionValuativeRel : ValuativeRel M :=
  letI := algebraicExtensionNormedField K M
  haveI := algebraicExtensionNormedField_isUltrametricDist K M
  ValuativeRel.ofValuation (NormedField.valuation (K := M))

end TauCeti
end
end
