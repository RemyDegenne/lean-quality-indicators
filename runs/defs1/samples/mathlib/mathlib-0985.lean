@[expose] public section

namespace Matrix

variable {α β m n : Type*} {A : Matrix n n α}

section Star

variable [Star α] [Star β]

/-- A matrix is Hermitian if it is equal to its conjugate transpose. On the reals, this definition
captures symmetric matrices. -/
def IsHermitian (A : Matrix n n α) : Prop := Aᴴ = A

end Star
end Matrix
end
