public section

variable {R M G : Type*}

export NoZeroSMulDivisors (eq_zero_or_eq_zero_of_smul_eq_zero)

theorem noZeroSMulDivisors_iff_right_eq_zero_of_smul [Zero R] [Zero M] [SMul R M] :
    NoZeroSMulDivisors R M ↔ ∀ r : R, r ≠ 0 → ∀ m : M, r • m = 0 → m = 0 := by
  simp_rw [noZeroSMulDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h r hr m eq ↦ h eq hr, fun h r m eq hr ↦ h r hr m eq⟩

end
