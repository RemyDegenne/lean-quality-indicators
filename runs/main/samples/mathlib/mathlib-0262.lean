@[expose] public section

open Function Set Filter Pointwise

variable {F α β γ : Type*}

namespace Filter

scoped[Pointwise] attribute [instance] Filter.instOne Filter.instZero

scoped[Pointwise] attribute [instance] one_neBot zero_neBot

scoped[Pointwise] attribute [instance] instInv instNeg

scoped[Pointwise] attribute [instance] inv.instNeBot neg.instNeBot

scoped[Pointwise] attribute [instance] Filter.instInvolutiveInv Filter.instInvolutiveNeg

scoped[Pointwise] attribute [instance] Filter.instMul Filter.instAdd

scoped[Pointwise] attribute [instance] mul.instNeBot add.instNeBot

scoped[Pointwise] attribute [instance] Filter.instDiv Filter.instSub

scoped[Pointwise] attribute [instance] div.instNeBot sub.instNeBot

scoped[Pointwise] attribute [instance] Filter.instNSMul Filter.instNPow
  Filter.instZSMul Filter.instZPow

scoped[Pointwise] attribute [instance] Filter.semigroup Filter.addSemigroup
  Filter.commSemigroup Filter.addCommSemigroup Filter.mulOneClass Filter.addZeroClass

scoped[Pointwise] attribute [instance] Filter.monoid Filter.addMonoid

scoped[Pointwise] attribute [instance] Filter.commMonoid Filter.addCommMonoid Filter.divisionMonoid
  Filter.subtractionMonoid Filter.divisionCommMonoid Filter.subtractionCommMonoid
  Filter.instDistribNeg

section SMul

variable [SMul α β] {f f₁ f₂ : Filter α} {g g₁ g₂ h : Filter β} {s : Set α} {t : Set β} {a : α}
  {b : β}

scoped[Pointwise] attribute [instance] Filter.instSMul Filter.instVAdd

@[to_additive (attr := simp)]
theorem smul_bot : f • (⊥ : Filter β) = ⊥ :=
  map₂_bot_right

end SMul
end Filter
end
