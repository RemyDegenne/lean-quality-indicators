@[expose] public section

variable {α m n R : Type*}

namespace Matrix

@[inherit_doc] scoped infixl:100 " ⊙ " => Matrix.hadamard

section BasicProperties

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

section trace

variable [Fintype m] [Fintype n]

variable (R) [NonUnitalSemiring α]

theorem sum_hadamard_eq : (∑ i : m, ∑ j : n, (A ⊙ B) i j) = trace (A * Bᵀ) :=
  rfl

end trace
end BasicProperties
end Matrix
end
