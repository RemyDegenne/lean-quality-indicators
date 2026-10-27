@[expose] public section

universe uR uG uV uW uU

namespace Representation

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}

section Semiring

variable [Semiring R] [Monoid G] [AddCommMonoid V] [Module R V]

/-- The submodule of vectors fixed by every element of a monoid representation. -/
def fixedSubmodule (ρ : Representation R G V) : Submodule R V where
  carrier := {v | ∀ g : G, ρ g v = v}
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by simp only [hv g, hw g, map_add]
  smul_mem' r v hv g := by simp only [hv g, map_smulₛₗ, RingHom.id_apply]

end Semiring
end Representation
end
