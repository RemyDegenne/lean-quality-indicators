public section

open Set Filter Function

namespace Filter

variable {α β γ : Type*} {ι : Sort*}

section lift

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Set α → Filter β}

theorem lift_lift_same_le_lift {g : Set α → Set α → Filter β} :
    (f.lift fun s => f.lift (g s)) ≤ f.lift fun s => g s s :=
  le_lift.2 fun _s hs => lift_le hs <| lift_le hs le_rfl

end lift
end Filter
end
