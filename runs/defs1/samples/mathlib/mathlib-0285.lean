@[expose] public section

open Nat Finsupp

namespace Nat

variable {a b n p : ℕ}

/-- Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not dividing `a`,
we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnPrimePow {motive : ℕ → Sort*} (zero : motive 0) (one : motive 1)
    (prime_pow_mul : ∀ a p n : ℕ, p.Prime → ¬p ∣ a → 0 < n → motive a → motive (p ^ n * a)) :
    ∀ a, motive a :=
  Nat.strongRec fun n ↦
    match n with
    | 0 => fun _ => zero
    | 1 => fun _ => one
    | k + 2 => fun hk => by
      letI p := (k + 2).minFac
      haveI hp : Prime p := minFac_prime (succ_succ_ne_one k)
      letI t := (k + 2).factorization p
      haveI hpt : p ^ t ∣ k + 2 := ordProj_dvd _ _
      haveI htp : 0 < t := hp.factorization_pos_of_dvd (k + 1).succ_ne_zero (k + 2).minFac_dvd
      convert prime_pow_mul ((k + 2) / p ^ t) p t hp _ htp (hk _ (Nat.div_lt_of_lt_mul _)) using 1
      · rw [Nat.mul_div_cancel' hpt]
      · rw [Nat.dvd_div_iff_mul_dvd hpt, ← Nat.pow_succ]
        exact pow_succ_factorization_not_dvd (k + 1).succ_ne_zero hp
      · simp [htp.ne', hp.one_lt]

end Nat
end
