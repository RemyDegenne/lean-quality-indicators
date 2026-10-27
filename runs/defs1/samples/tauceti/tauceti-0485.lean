public section

open scoped MonoidAlgebra

namespace TauCeti

namespace Representation

universe u v w

variable {k : Type u} {G : Type v} {V : Type w} {W : Type*}

variable [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

variable (ρ : Representation k G V) (σ : Representation k G W)

section Idempotent

variable [Fintype G]

variable [FiniteDimensional k V] [FiniteDimensional k W] [IsAlgClosed k]

variable [Invertible (Nat.card G : k)] [ρ.IsIrreducible] [σ.IsIrreducible]

/-- The primitive central idempotent, read as an element of the centre of the group algebra. -/
noncomputable def primitiveCentralIdempotentCenter : Subalgebra.center k k[G] :=
  ⟨primitiveCentralIdempotent ρ, primitiveCentralIdempotent_mem_center ρ⟩

end Idempotent
end Representation
end TauCeti
end
