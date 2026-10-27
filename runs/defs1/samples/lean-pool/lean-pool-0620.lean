@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits ZeroObject

open scoped MonObj

universe v u w

section SimpleSum

variable {E : Type u}

/-- The direct sum of `p` copies of `X` and `q` copies of `Y`. -/
noncomputable def mixSum [Category.{v} E] [Abelian E]
    (X Y : E) (p q : ℕ) : E :=
  idxSum (id : E → E) (List.replicate p X ++ List.replicate q Y)

end SimpleSum
end RS
end
