@[expose] public section

open Real

noncomputable section

namespace Real

namespace Angle

theorem nsmul_toReal_eq_mul {n : ℕ} (h : n ≠ 0) {θ : Angle} :
    (n • θ).toReal = n * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / n) (π / n) := by
  nth_rw 1 [← coe_toReal θ]
  have h' : 0 < (n : ℝ) := mod_cast Nat.pos_of_ne_zero h
  rw [← coe_nsmul, nsmul_eq_mul, toReal_coe_eq_self_iff, Set.mem_Ioc, div_lt_iff₀' h',
    le_div_iff₀' h']

end Angle
end Real
end
end
