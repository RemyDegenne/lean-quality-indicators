@[expose] public section

variable {α β : Type*} {rα : α → α → Prop} {rβ : β → β → Prop} {a : α} {b : β}

namespace Prod

theorem GameAdd.recursion_eq {C : α → β → Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
    GameAdd.recursion hα hβ IH a b = IH a b fun a' b' _ => GameAdd.recursion hα hβ IH a' b' :=
  WellFounded.fix_eq _ _ _

end Prod
end
