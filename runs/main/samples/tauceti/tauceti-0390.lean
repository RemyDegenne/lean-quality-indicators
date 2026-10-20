public section

namespace WeierstrassCurve

open IsLocalRing Polynomial TauCeti

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {ϖ : R}

theorem natCard_tateCubicRoots_le (hϖ : Prime ϖ) (h₂ : ϖ ∣ W.a₂) (h₄ : ϖ ^ 2 ∣ W.a₄)
    (h₆ : ϖ ^ 3 ∣ W.a₆) : Nat.card (W.tateCubicRoots ϖ) ≤ 3 := by
  classical
  obtain ⟨b₂, h₂⟩ := h₂
  obtain ⟨b₄, h₄⟩ := h₄
  obtain ⟨b₆, h₆⟩ := h₆
  have : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).2 hϖ
  set P : (R ⧸ Ideal.span {ϖ})[X] := X ^ 3 + C (Ideal.Quotient.mk _ b₂) * X ^ 2 +
    C (Ideal.Quotient.mk _ b₄) * X + C (Ideal.Quotient.mk _ b₆)
  have hP : P.Monic := by unfold P; monicity!
  have hdeg : P.natDegree = 3 := by unfold P; compute_degree!
  have hset : W.tateCubicRoots ϖ = ↑P.roots.toFinset := by
    ext t
    rw [mem_tateCubicRoots_iff hϖ.ne_zero h₂ h₄ h₆, Finset.mem_coe, Multiset.mem_toFinset,
      mem_roots hP.ne_zero]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (hdeg ▸ card_roots' P)

end Domain
end WeierstrassCurve
end
