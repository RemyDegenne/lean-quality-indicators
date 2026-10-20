set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace CountableEndomorphism

universe u v

variable (S : Type u) (M : Type v) [Semiring S] [AddCommGroup M] [Module S M]

/-- The unary row given by extracting even coordinates. -/
noncomputable def row : Fin 1 → Module.End S (ℕ →₀ M) := fun _ => y₀ S M

end CountableEndomorphism
end
