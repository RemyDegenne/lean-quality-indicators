@[expose] public section

variable {α : Type*}

section RelPrime

variable [CommMonoid α] {x y z : α}

theorem IsRelPrime.mul_dvd_of_right_isPrimal (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
    (hy : IsPrimal y) : x * y ∣ z := by
  obtain ⟨w, rfl⟩ := H1
  exact mul_dvd_mul_left x (H.symm.dvd_of_dvd_mul_left_of_isPrimal H2 hy)

end RelPrime
end
