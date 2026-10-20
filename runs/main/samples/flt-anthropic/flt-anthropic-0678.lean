namespace P2MW.S_ModularCurve_genusFormula_isNat

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

namespace ModularCurve

p2m_open

section Prime

variable {p : ℕ}

theorem sq_add_self_add_one_eq_zero_iff_orderOf_eq_three (hp : p.Prime) (hp3 : p ≠ 3)
    (x : ZMod p) : x ^ 2 + x + 1 = 0 ↔ orderOf x = 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  constructor
  · intro hx
    refine orderOf_eq_prime ?_ ?_
    ·
      linear_combination (x - 1) * hx
    ·
      rintro rfl
      have h3 : (3 : ZMod p) = 0 := by linear_combination hx
      have hcast : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
      have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp hcast
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd)
  · intro hx
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      omega
    have hfac : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h : x = 1) hx1
    · exact h

end Prime
end ModularCurve
end P2MW.S_ModularCurve_genusFormula_isNat
