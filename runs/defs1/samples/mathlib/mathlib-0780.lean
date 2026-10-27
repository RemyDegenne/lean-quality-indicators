@[expose] public section

open Set Function Equiv

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s t u : Set α}

@[inherit_doc]
infixl:25 " ≃ᵐ " => MeasurableEquiv

section curry

namespace MeasurableEquiv

/-- The currying operation `Sigma.curry` as a measurable equivalence.
See `MeasurableEquiv.piCurry` for the dependent version. -/
@[simps!]
def curry (ι κ X : Type*) [MeasurableSpace X] : (ι × κ → X) ≃ᵐ (ι → κ → X) where
  toEquiv := Equiv.curry ι κ X

end MeasurableEquiv
end curry
end
