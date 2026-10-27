@[expose] public section

universe u v w x

infixr:25 " ↪ " => Embedding

namespace Function

namespace Embedding

/-- A right inverse `surjInv` of a surjective function as an `Embedding`. -/
protected noncomputable def ofSurjective {α β} (f : β → α) (hf : Surjective f) : α ↪ β :=
  ⟨surjInv hf, injective_surjInv _⟩

end Embedding
end Function
end
