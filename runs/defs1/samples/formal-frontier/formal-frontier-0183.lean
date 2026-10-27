set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace CountableEndomorphism

universe u v

variable (S : Type u) (M : Type v) [Semiring S] [AddCommGroup M] [Module S M]

/-- The two-column matrix of even and odd embeddings. -/
noncomputable def rectangularColumn :
    Matrix (Fin 1) (Fin 2) (Module.End S (ℕ →₀ M)) :=
  fun _ i => Fin.cases (x₀ S M) (fun _ => x₁ S M) i

end CountableEndomorphism
end
