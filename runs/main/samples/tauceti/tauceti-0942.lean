public section

namespace TauCeti

variable {p : ℕ}

section Monoid

variable {G : Type*} [Monoid G] {x : G}

section Order

theorem eq_pFreePart (hp : p.Prime) {s u : G} (hsu : Commute s u) (hmul : s * u = x)
    (hs : ¬ p ∣ orderOf s) {k : ℕ} (hu : orderOf u = p ^ k) : s = pFreePart p x := by
  have hs0 : orderOf s ≠ 0 := fun h => hs (by rw [h]; exact dvd_zero p)
  have hcop : Nat.Coprime (orderOf s) (orderOf u) :=
    hu ▸ ((Nat.Prime.coprime_iff_not_dvd hp).2 hs).symm.pow_right k
  have hord : orderOf x = orderOf s * p ^ k := by
    rw [← hmul, hsu.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hu]
  have hx : orderOf x ≠ 0 := by
    rw [hord]; exact Nat.mul_ne_zero hs0 (pow_ne_zero k hp.pos.ne')
  have hfac : (orderOf x).factorization p = k := by
    rw [hord, Nat.factorization_mul hs0 (pow_ne_zero k hp.pos.ne'), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hs, hp.factorization_pow, Finsupp.single_eq_same,
      zero_add]
  have hu1 : u ^ pFreeExponent p x = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.1 ?_
    rw [hu, ← hfac]
    exact ordProj_dvd_pFreeExponent hx
  have hs1 : s ^ pFreeExponent p x = s := by
    have h1 : 1 ≤ pFreeExponent p x := Nat.one_le_iff_ne_zero.2 pFreeExponent_ne_zero
    obtain ⟨d, hd⟩ : ∃ d, pFreeExponent p x = d + 1 := ⟨pFreeExponent p x - 1, by omega⟩
    have hcompl : ordCompl[p] (orderOf x) = orderOf s := by
      rw [hfac, hord]
      exact Nat.mul_div_cancel _ (pow_pos hp.pos k)
    have hsd : s ^ d = 1 := by
      refine orderOf_dvd_iff_pow_eq_one.1 ?_
      have hdvd := ordCompl_dvd_pFreeExponent_sub_one hp hx
      rwa [hcompl, hd, Nat.add_sub_cancel] at hdvd
    rw [hd, pow_succ, hsd, one_mul]
  rw [pFreePart, ← hmul, hsu.mul_pow, hmul, hu1, mul_one, hs1]

end Order
end Monoid
end TauCeti
end
