@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*}

namespace SetRel

variable {R R₁ R₂ : SetRel α β} {S : SetRel β γ} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {u : Set γ}
  {a a₁ a₂ : α} {b : β} {c : γ}

scoped notation:50 a:50 " ~[" R "] " b:50 => (a, b) ∈ R

@[inherit_doc] scoped infixl:62 " ○ " => comp

lemma iUnion_comp (R : ι → SetRel α β) (S : SetRel β γ) : (⋃ i, R i) ○ S = ⋃ i, R i ○ S := by
  grind [Set.mem_iUnion]

end SetRel
end
