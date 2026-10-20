@[expose] public section

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

notation3 "Π₀ "(...)", "r:(scoped f => DFinsupp f) => r

namespace DFinsupp

section Basic

variable [∀ i, Zero (β i)]

variable [DecidableEq ι]

theorem single_injective {i} : Function.Injective (single i : β i → Π₀ i, β i) := fun _ _ H =>
  Pi.single_injective i <| DFunLike.coe_injective.eq_iff.mpr H

end Basic
end DFinsupp
end
