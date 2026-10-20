@[expose] public section

variable {α β : Type*}

open Nat

section Monoid

variable [Monoid α] [Monoid β] {a b : α}

theorem FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd (hfin : FiniteMultiplicity a b) :
    ∃ c : α, b = a ^ multiplicity a b * c ∧ ¬a ∣ c := by
  obtain ⟨c, hc⟩ := pow_multiplicity_dvd a b
  refine ⟨c, hc, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk, ← mul_assoc, ← _root_.pow_succ] at hc
  have h₁ : a ^ (multiplicity a b + 1) ∣ b := ⟨k, hc⟩
  exact (hfin.multiplicity_eq_iff.1 (by simp)).2 h₁

end Monoid
end
