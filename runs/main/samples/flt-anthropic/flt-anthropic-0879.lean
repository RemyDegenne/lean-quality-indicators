namespace P2MW.S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval

set_option autoImplicit false

open Polynomial

namespace P2mResNorm

variable {p : ℕ} [Fact p.Prime]

theorem mem_span_pow_of_le {x : ℤ_[p]} {L M : ℕ} (hML : M ≤ L)
    (h : x ∈ Ideal.span {(p : ℤ_[p]) ^ L}) : x ∈ Ideal.span {(p : ℤ_[p]) ^ M} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  exact (pow_dvd_pow _ hML).trans h

end P2mResNorm
end P2MW.S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval
