@[expose] public section

universe u v w x

variable {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {γ δ : Type*}

namespace Sum

theorem inl_injective : Function.Injective (inl : α → α ⊕ β) := fun _ _ ↦ inl.inj

end Sum
end
