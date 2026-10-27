public section

namespace TauCeti

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
  [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

section GeneralAction

variable [MulDistribMulAction G kˣ]

section Linearization

variable {α : FactorSet G kˣ} {ρ : G → V ≃ₗ[k] V}

namespace IsProjectiveRep

variable (hρ : IsProjectiveRep ρ (Function.curry ⇑α)) (htriv : ∀ (g : G) (a : kˣ), g • a = a)

/-- The linearization, packaged as a `Representation` of the central extension `E_α` on `V`, so
that the machinery written against `Representation` applies to it. -/
def linearizationRepresentation : Representation k α.Extension V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (hρ.linearization htriv)

end IsProjectiveRep
end Linearization
end GeneralAction
end TauCeti
end
