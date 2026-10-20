public section

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] (A B : R)

section CInvariants

variable {K : Type*} [Field K]

variable [Invertible (2 : K)] [Invertible (3 : K)]

variable (c₄ c₆ : K)

@[simp] lemma ofCInvariants_c₄ : (ofCInvariants c₄ c₆).c₄ = c₄ := by
  have h48 : (48 : K) ≠ 0 :=
    TauCeti.ne_zero_of_eq_two_pow_mul_three_pow (m := 4) (n := 1) (by norm_num)
  rw [ofCInvariants_eq_shortCurve, c₄_of_isShortNF, shortCurve_a₄]
  field_simp

end CInvariants
end WeierstrassCurve
end
