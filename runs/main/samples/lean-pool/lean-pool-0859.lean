@[expose] public section

universe u

noncomputable section

open Cardinal Ideal

variable {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

theorem combined_step_card
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (ℓ : T ⧸ IsLocalRing.maximalIdeal T ^ 2)
    (q : Ideal T) (hq_prime : q.IsPrime) (hq_ne_bot : q ≠ ⊥)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T)) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      (∃ (c : S.carrier),
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (c : T) = ℓ) ∧
      (∃ (t : S.carrier), (t : T) ∈ q ∧ (t : T) ≠ 0) ∧
      (∀ (I : Ideal S.carrier), I.FG →
        ∀ (c : S.carrier), (c : T) ∈ Ideal.map S.carrier.subtype I → c ∈ I) ∧
      (Cardinal.mk S.carrier < Cardinal.mk T) := by
  obtain ⟨S, hAext, hℓ, hq, hclose⟩ := combined_step R ℓ q hq_prime hq_ne_bot
    hM_not_assoc hAss_ht hR_card hT_card hT_aleph0
  exact ⟨S, hAext, hℓ, hq, hclose,
    lt_of_le_of_lt hAext.card_le (max_lt hT_aleph0 hR_card)⟩

end
end
