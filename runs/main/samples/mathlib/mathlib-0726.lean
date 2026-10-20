@[expose] public section

variable {F α β : Type*}

section Semiring

variable [Semiring α] [Semiring β] {a b : α} {n : ℕ}

@[simp] lemma odd_one : Odd (1 : α) :=
  ⟨0, (zero_add _).symm.trans congr($((mul_zero _).symm) + (1 : α))⟩

end Semiring
end
