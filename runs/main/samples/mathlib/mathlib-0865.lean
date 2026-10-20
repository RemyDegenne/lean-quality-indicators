@[expose] public section

namespace Matrix

variable {α β m n : Type*} {A : Matrix n n α}

section Star

variable [Star α] [Star β]

theorem IsHermitian.eq {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ = A := h

end Star
end Matrix
end
