@[expose] public section

variable {F α β : Type*}

section Semiring

variable [Semiring α] [Semiring β] {a b : α} {n : ℕ}

lemma even_iff_two_dvd : Even a ↔ 2 ∣ a := by simp [Even, Dvd.dvd, two_mul]

end Semiring
end
