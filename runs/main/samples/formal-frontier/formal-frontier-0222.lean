@[expose] public section

namespace ToricIdeals.RationalNormalCurve

open MvPolynomial

noncomputable section

universe u v

theorem quotientHomogeneousBasis_mul (R : Type u) [CommRing R] (n d e : ℕ)
    (i : Fin (n * d + 1)) (j : Fin (n * e + 1)) :
    let k : Fin (n * (d + e) + 1) :=
      ⟨i.val + j.val, Nat.lt_succ_of_le (by
        simpa only [Nat.mul_add] using
          Nat.add_le_add (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt))⟩
    (quotientHomogeneousBasis R n d i : Source R n ⧸ hankelIdeal R n) *
        (quotientHomogeneousBasis R n e j : Source R n ⧸ hankelIdeal R n) =
      (quotientHomogeneousBasis R n (d + e) k : Source R n ⧸ hankelIdeal R n) := by
  dsimp only
  by_cases hn0 : n = 0
  · subst n
    simp only [quotientHomogeneousBasis_zero_apply, ← map_mul, ← pow_add]
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hvector (a : ℕ) (l : Fin (n * a + 1)) :
        quotientCoefficientEmbedding R n hn
            (quotientHomogeneousBasis R n a l : Source R n ⧸ hankelIdeal R n) =
          monomial (Finsupp.single 0 (n * a - l.val) + Finsupp.single 1 l.val) 1 := by
      rw [quotientHomogeneousBasis_apply_of_pos R n a hn,
        quotientCoefficientEmbedding_mk, rncMap_monomial]
      have h := (fiberNormalExponent_degree R n a hn
        ((twoExponentIndex (n * a)).symm l).1 ((twoExponentIndex (n * a)).symm l).2).2
      simpa only [twoExponentIndex_symm] using
        congrArg (fun t : Fin 2 →₀ ℕ => monomial t (1 : R)) h
    apply quotientCoefficientEmbedding_injective R n hn
    simp only [map_mul, hvector, monomial_mul_monomial, mul_one]
    apply congrArg (fun t : Fin 2 →₀ ℕ => monomial t (1 : R))
    have hi : i.val ≤ n * d := Nat.le_of_lt_succ i.isLt
    have hj : j.val ≤ n * e := Nat.le_of_lt_succ j.isLt
    have hdiff : n * d - i.val + (n * e - j.val) =
        n * (d + e) - (i.val + j.val) := by
      rw [Nat.mul_add]
      omega
    ext a
    fin_cases a <;> simp [hdiff]

end
end ToricIdeals.RationalNormalCurve
end
