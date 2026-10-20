@[expose] public section

variable {α : Sort*} {β : Sort*}

namespace Quot

variable {ra : α → α → Prop} {rb : β → β → Prop} {φ : Quot ra → Quot rb → Sort*}

@[inherit_doc Quot.mk]
local notation3:arg "⟦" a "⟧" => Quot.mk _ a

variable {γ : Sort*} {r : α → α → Prop} {s : β → β → Prop}

variable {t : γ → γ → Prop}

/-- A binary version of `Quot.recOnSubsingleton`. -/
@[elab_as_elim]
protected def recOnSubsingleton₂ {φ : Quot r → Quot s → Sort*}
    [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)] (q₁ : Quot r)
    (q₂ : Quot s) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  @Quot.recOnSubsingleton _ r (fun q ↦ φ q q₂)
    (fun a ↦ Quot.ind (β := fun b ↦ Subsingleton (φ (mk r a) b)) (h a) q₂) q₁
    fun a ↦ Quot.recOnSubsingleton q₂ fun b ↦ f a b

end Quot
end
