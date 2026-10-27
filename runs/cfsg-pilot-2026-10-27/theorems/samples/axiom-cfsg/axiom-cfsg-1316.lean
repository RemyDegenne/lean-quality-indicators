public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup

variable {n : ℕ}

theorem sign_foldl_swaps [NeZero n] (sw : List (ℕ × ℕ))
    (hsw : ∀ p ∈ sw, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2) :
    ∀ σ : Perm (Fin n),
      sign (sw.foldl (fun σ p => σ * swap (Fin.ofNat n p.1) (Fin.ofNat n p.2)) σ) =
        sign σ * (-1) ^ sw.length := by
  induction sw with
  | nil => intro σ; simp
  | cons p sw ih =>
    intro σ
    have hp := hsw p List.mem_cons_self
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (fun q hq => hsw q (List.mem_cons_of_mem _ hq)), Perm.sign_mul,
      Perm.sign_swap]
    · rw [pow_succ]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    · rw [fin_ofNat_eq hp.1, fin_ofNat_eq hp.2.1]
      exact fun h => hp.2.2 (congrArg Fin.val h)

end CFSG.OddStandard.Solomon75.AhatData
end
