namespace P2MW.S_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

p2m_open

namespace WeierstrassCurve

namespace SupersingularFrobeniusInteger

p2m_open

section InjectivePolynomial

variable {k : Type*} [Field k]

theorem coeff_X_sub_C_pow_pow_mul (p : ℕ) [Fact p.Prime] [CharP k p] (t m : ℕ) (hm : 1 ≤ m)
    (x₀ : k) :
    ((X - C x₀ : k[X]) ^ (p ^ t * m)).coeff (p ^ t * (m - 1)) = -(x₀ ^ p ^ t) * (m : k) := by
  have hp : 0 < p ^ t := pow_pos (Nat.Prime.pos Fact.out) t
  rw [pow_mul, sub_pow_char_pow, ← C_pow]
  have hexp : (X ^ p ^ t - C (x₀ ^ p ^ t) : k[X]) ^ m =
      expand k (p ^ t) ((X - C (x₀ ^ p ^ t)) ^ m) := by
    rw [map_pow (expand k (p ^ t)), map_sub (expand k (p ^ t)), expand_X, expand_C]
  rw [hexp, mul_comm (p ^ t) (m - 1), coeff_expand_mul hp, sub_eq_add_neg, ← C_neg,
    coeff_X_add_C_pow]
  have h1 : m - (m - 1) = 1 := by omega
  have h2 : m.choose (m - 1) = m := by
    rw [Nat.choose_symm hm, Nat.choose_one_right]
  rw [h1, pow_one, h2]

end InjectivePolynomial
end SupersingularFrobeniusInteger
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
