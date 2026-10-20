namespace P2MW.S_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange

set_option autoImplicit false

open TensorProduct

universe u

namespace TorsorRank

theorem isLocalRing_quotient_maximal_pow {R : Type*} [CommRing R] (m : Ideal R) [hm : m.IsMaximal] {n : ℕ}
    (hn : n ≠ 0) : IsLocalRing (R ⧸ m ^ n) := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk (m ^ n)) := Ideal.Quotient.mk_surjective
  have hbot : Ideal.comap (Ideal.Quotient.mk (m ^ n)) ⊥ = m ^ n := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  refine IsLocalRing.of_unique_max_ideal ⟨m.map (Ideal.Quotient.mk (m ^ n)), ?_, ?_⟩
  · rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm with h | h
    · exfalso
      have := congrArg (Ideal.comap (Ideal.Quotient.mk (m ^ n))) h
      rw [Ideal.comap_map_of_surjective _ hsurj, hbot, Ideal.comap_top,
        sup_eq_left.mpr (Ideal.pow_le_self hn)] at this
      exact hm.ne_top this
    · exact h
  · intro J hJ
    have hJ' : (J.comap (Ideal.Quotient.mk (m ^ n))).IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
    have hle : m ≤ J.comap (Ideal.Quotient.mk (m ^ n)) := by
      rw [← Ideal.IsPrime.pow_le_iff (I := m) hn]
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact J.zero_mem
    have heq : J.comap (Ideal.Quotient.mk (m ^ n)) = m := (hm.eq_of_le hJ'.ne_top hle).symm
    rw [← Ideal.map_comap_of_surjective _ hsurj J, heq]

end TorsorRank
end P2MW.S_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange
