public section

namespace TauCeti

namespace Nat

theorem gcd_eq_gcd_ordCompl_mul_pow_min {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hn : n ≠ 0) :
    Nat.gcd m n = Nat.gcd (ordCompl[p] m) (ordCompl[p] n) *
      p ^ min (m.factorization p) (n.factorization p) := by
  have hm_eq : m = p ^ m.factorization p * ordCompl[p] m :=
    (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hn_eq : n = p ^ n.factorization p * ordCompl[p] n :=
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  conv_lhs => rw [hm_eq, hn_eq]
  exact gcd_pow_mul_pow_mul hp (Nat.not_dvd_ordCompl hp hm) (Nat.not_dvd_ordCompl hp hn)

end Nat
end TauCeti
end
