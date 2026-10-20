namespace P2MW.S_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 800000

open ValuationSubring

noncomputable section

namespace WittUnramSol

variable (p : ℕ) [hp : Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

section OverP

variable (hA : A.LiesOverPrime p)

include hA

theorem exists_pow_mem_span_p (x : ↥(OA A)) (hx : x ∈ IsLocalRing.maximalIdeal ↥(OA A)) :
    ∃ n : ℕ, x ^ n ∈ Ideal.span {((p : ℕ) : ↥(OA A))} := by
  rw [mem_maximalIdeal_iff] at hx
  obtain ⟨n, hn⟩ := rankOne p A hA (x : CA A) _ hx (p_ne_zero p A hA)
  refine ⟨n, ?_⟩
  rw [← pow_one ((p : ℕ) : ↥(OA A)), mem_span_pow_iff p A hA, pow_one, SubmonoidClass.coe_pow, map_pow]
  exact hn

end OverP
end WittUnramSol
end
end P2MW.S_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime
