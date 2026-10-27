@[expose] public section

section Ring

variable (M R : Type*) [Monoid M] [Ring R] [MulSemiringAction M R]

variable (S : Subring R)

open MulAction

variable {R}

/-- A typeclass for subrings invariant under a `MulSemiringAction`. -/
class IsInvariantSubring : Prop where
  smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S

end Ring
end
