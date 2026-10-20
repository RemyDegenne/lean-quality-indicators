namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node

set_option autoImplicit false

open scoped TensorProduct

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace B25N3

variable (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]

theorem algebraMap_pow_p (a : ℤ_[p]) : (algebraMap ℤ_[p] κ a) ^ p = algebraMap ℤ_[p] κ a := by
  have hmem : a ^ p - a ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card,
      sub_self]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  have : algebraMap ℤ_[p] κ (a ^ p - a) = 0 := by rw [← hb, map_mul, algebraMap_p_eq_zero, mul_zero]
  rwa [map_sub, map_pow, sub_eq_zero] at this

end B25N3
end P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node
