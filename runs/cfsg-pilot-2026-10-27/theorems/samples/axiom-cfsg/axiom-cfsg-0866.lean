public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem apply_mul_apply_sq_sub_of_orderOf_eq_five (hp : p ≠ 2) (hp5 : p ≠ 5) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (h : orderOf (Module.reflection hφ * Module.reflection hψ) = 5) :
    (φ b * ψ a) ^ 2 - 3 * (φ b * ψ a) + 1 = 0 := by
  have h5 : (Module.reflection hφ * Module.reflection hψ) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (Module.reflection hφ * Module.reflection hψ)
    rwa [h] at this
  have hneq : Module.reflection hφ * Module.reflection hψ ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at h; norm_num at h
  have : NeZero (2 : ZMod p) := ⟨ZMod.prime_ne_zero p 2 hp⟩
  rcases linearIndependent_and_or_exists_transvection (K := ZMod p) hφ hψ with
    ⟨hxy, hfg⟩ | ⟨w, χ, hχw, hN⟩
  · have hcrit := (reflection_mul_reflection_pow_eq_one_iff hφ hψ hxy hfg 5).mp h5
    have hAB : ggCoxA (ZMod p) 5 (φ b * ψ a - 2) + ggCoxB (ZMod p) 5 (φ b * ψ a - 2)
        = ((φ b * ψ a - 2) ^ 2 + (φ b * ψ a - 2) - 1) ^ 2 := by
      simp only [ggCoxA, ggCoxB]
      norm_num
      rw [Polynomial.Chebyshev.S_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one]
      ring
    have hsq : ((φ b * ψ a - 2) ^ 2 + (φ b * ψ a - 2) - 1) ^ 2 = 0 := by
      rw [← hAB]; exact hcrit.1
    have hlin : (φ b * ψ a - 2) ^ 2 + (φ b * ψ a - 2) - 1 = 0 := by
      rw [pow_two] at hsq
      exact mul_self_eq_zero.mp hsq
    linear_combination hlin
  · exfalso
    have h5zero : (5 : ZMod p) = 0 := natCast_eq_zero_of_unipotent hχw hN hneq h5
    have hdvd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp h5zero
    have hpprime : p.Prime := Fact.out
    have hpge : 2 ≤ p := hpprime.two_le
    have hple : p ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p
    · exact hp rfl
    · norm_num at hdvd
    · norm_num at hpprime
    · exact hp5 rfl

end CFSG.StandardType.ZS
end
