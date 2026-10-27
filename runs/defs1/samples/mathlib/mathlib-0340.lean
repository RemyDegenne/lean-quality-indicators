@[expose] public section

open Set Function

open scoped symmDiff

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type x}

namespace Set

section FintypeInstances

/-- If `(Set.univ : Set α)` is finite then `α` is a finite type. -/
@[instance_reducible]
noncomputable def fintypeOfFiniteUniv (H : (univ (α := α)).Finite) : Fintype α :=
  @Fintype.ofEquiv _ (univ : Set α) H.fintype (Equiv.Set.univ _)

end FintypeInstances
end Set
end
