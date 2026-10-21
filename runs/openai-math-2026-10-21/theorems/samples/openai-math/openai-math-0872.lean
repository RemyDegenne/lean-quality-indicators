namespace OAI

open scoped BigOperators Classical

namespace DukePrimeDegree

theorem cyclic_permutation_character_identity_inside
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (a : CyclicSubgroups H → ℤ)
    (ha : ∀ h : H, (∑ C, if h ∈ C.val then a C else 0) = 1) :
    ∀ g : G,
      (∑ C, ((a C * Fintype.card (C.val.map H.subtype) : ℤ) : ℂ) *
        (Representation.ofMulAction ℂ G (G ⧸ C.val.map H.subtype)).character g) =
      Fintype.card H * (Representation.ofMulAction ℂ G (G ⧸ H)).character g := by
  intro g
  have hs (x : G) : (∑ C : CyclicSubgroups H, (a C : ℂ) *
      (if x⁻¹ * g * x ∈ C.val.map H.subtype then (1 : ℂ) else 0)) =
      if x⁻¹ * g * x ∈ H then 1 else 0 := by
    have he := cyclic_indicator_inside_subgroup H a ha (x⁻¹ * g * x)
    have he' : (∑ C : CyclicSubgroups H,
        if x⁻¹ * g * x ∈ C.val.map H.subtype then (a C : ℂ) else 0) =
        if x⁻¹ * g * x ∈ H then (1 : ℂ) else 0 := by
      exact_mod_cast he
    simpa only [mul_ite, mul_one, mul_zero] using he'
  calc
    _ = ∑ C : CyclicSubgroups H, (a C : ℂ) *
        ∑ x : G, if x⁻¹ * g * x ∈ C.val.map H.subtype then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      rw [Int.cast_mul, Int.cast_natCast, conjugacy_indicator_sum_eq_card_mul_character]
      ring
    _ = ∑ x : G, ∑ C : CyclicSubgroups H, (a C : ℂ) *
        (if x⁻¹ * g * x ∈ C.val.map H.subtype then (1 : ℂ) else 0) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ x : G, if x⁻¹ * g * x ∈ H then (1 : ℂ) else 0 := by
      simp only [hs]
    _ = _ := conjugacy_indicator_sum_eq_card_mul_character H g

end DukePrimeDegree
end OAI
