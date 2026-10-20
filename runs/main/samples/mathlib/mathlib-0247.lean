public section

universe u

variable {α : Type u}

export ExistsMulOfLE (exists_mul_of_le)

export ExistsAddOfLE (exists_add_of_le)

section MulOneClass

variable [MulOneClass α] [Preorder α] [ExistsMulOfLE α] {a b : α}

@[to_additive] lemma exists_one_lt_mul_of_lt' [MulLeftReflectLT α] (h : a < b) :
    ∃ c, 1 < c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h.le; exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩

end MulOneClass
end
