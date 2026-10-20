namespace P2MW.S_ModularCurve_exists_variableChange_veluQuotient_toricSlotSet

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve

p2m_open

section ConstBlocks

open WeierstrassCurve Polynomial

section HalfPairing

variable (K : Type*) [Field K]

theorem sum_full_eq_two_half (p : ℕ) (hp : Odd p) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (f : K → K) (hf : ∀ c : K, c ≠ 0 → f c⁻¹ = f c) :
    ∑ j ∈ Finset.Ico 1 p, f ((ζ : K) ^ j) =
      2 * ∑ k ∈ Finset.Icc 1 (p / 2), f ((ζ : K) ^ k) := by
  rw [sum_Ico_eq_sum_half_pair p hp (fun j => f ((ζ : K) ^ j)), two_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  rcases eq_or_ne p 1 with rfl | hp1
  · omega
  have hp2 : 2 ≤ p := by obtain ⟨q, rfl⟩ := hp; omega
  rw [← inv_zetaPow K p ζ hζ hk.1 (by omega), hf _ (pow_ne_zero k ζ.ne_zero)]

end HalfPairing
end ConstBlocks
end ModularCurve
end
end P2MW.S_ModularCurve_exists_variableChange_veluQuotient_toricSlotSet
