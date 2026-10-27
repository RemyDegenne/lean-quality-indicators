@[expose] public section

open CategoryTheory

universe u v

attribute [instance] ωCPO.str

namespace ωCPO

open OmegaCompletePartialOrder

section

open CategoryTheory.Limits

namespace HasEqualizers

/-- The equalizer inclusion function as a `ContinuousHom`. -/
def equalizerι {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f g : α →𝒄 β) : { a : α // f a = g a } →𝒄 α :=
  .mk (OrderHom.Subtype.val _) fun _ => rfl

end HasEqualizers
end
end ωCPO
end
