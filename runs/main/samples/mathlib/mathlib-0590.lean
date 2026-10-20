@[expose] public section

variable {α β : Type*}

open Nat

section CancelCommMonoidWithZero

variable [CommMonoidWithZero α] [IsCancelMulZero α]

@[simp]
theorem multiplicity_self {a : α} (ha : FiniteMultiplicity a a) : multiplicity a a = 1 := by
  rw [ha.multiplicity_eq_iff]
  simp only [pow_one, dvd_refl, reduceAdd, true_and]
  rintro ⟨v, hv⟩
  nth_rw 1 [← mul_one a] at hv
  simp only [sq, mul_assoc, mul_eq_mul_left_iff] at hv
  obtain hv | rfl := hv
  · have : IsUnit a := .of_mul_eq_one v hv.symm
    simpa [this] using ha.not_isUnit
  · simpa using ha.ne_zero

end CancelCommMonoidWithZero
end
