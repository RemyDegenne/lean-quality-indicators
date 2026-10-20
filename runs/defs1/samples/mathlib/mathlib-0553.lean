@[expose] public section

universe u v w

variable {α : Sort*}

namespace Function

variable {β : Sort*} {f : α → β}

/-- If the domain of a surjective function is a singleton,
then the codomain is a singleton as well. -/
@[instance_reducible]
protected def Surjective.unique {α : Sort u} (f : α → β) (hf : Surjective f) [Unique.{u} α] :
    Unique β :=
  @Unique.mk' _ ⟨f default⟩ hf.subsingleton

end Function
end
