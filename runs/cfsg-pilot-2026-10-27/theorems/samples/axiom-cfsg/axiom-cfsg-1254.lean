public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A312Sub

open CFSG.Open CFSG.Quasithin

open CFSG.QuasithinUnique.Vol2Native.A312L

theorem K_small
    {G : Type} [Group G] [Finite G] {K : Subgroup G} (hKl : IsListed25 K)
    (hKnb : ¬ fusionIsBenderGroup ↥K) {N : ℕ} (hN : N = 360 ∨ N = 5616 ∨ N = 7920)
    (hdvd : Nat.card ↥K ∣ N) :
    Nat.card ↥K = N ∨ (N = 7920 ∧ Nonempty (↥K ≃* alternatingGroup (Fin 6))) := by
  have h7 : ¬ 7 ∣ N := by rcases hN with rfl | rfl | rfl <;> norm_num
  have h32 : ¬ 32 ∣ N := by rcases hN with rfl | rfl | rfl <;> norm_num
  rcases hKl with hB | hR | ⟨h33 | ⟨⟨e⟩⟩⟩ | ⟨p, hpf, hp7, hp⟩
  · exact absurd hB hKnb
  · rcases hR with ⟨n, -, h⟩ | ⟨n, hn, h⟩ | ⟨⟨e⟩⟩ | h
    · exact absurd ((seven_dvd_card_psl_three_even h).trans hdvd) h7
    · exact absurd ((thirtytwo_dvd_card_psp_four_even hn h).trans hdvd) h32
    · have hK : Nat.card ↥K = 360 := (Nat.card_congr e.toEquiv).trans card_alt_six_loc
      rw [hK] at hdvd ⊢
      rcases hN with rfl | rfl | rfl
      · exact Or.inl rfl
      · omega
      · exact Or.inr ⟨rfl, ⟨e⟩⟩
    · have h1 := seven_dvd_card_psl_three_even h
      exact absurd (h1.trans ((Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K)).trans hdvd)) h7
  · have hK := card_psl_three_three h33
    rw [hK] at hdvd ⊢
    rcases hN with rfl | rfl | rfl
    · omega
    · exact Or.inl rfl
    · omega
  · have hK : Nat.card ↥K = 7920 := (Nat.card_congr e.toEquiv).trans
      CFSG.Semidihedral.GL2Recognition.card_nativeM11
    rw [hK] at hdvd ⊢
    rcases hN with rfl | rfl | rfl
    · omega
    · omega
    · exact Or.inl rfl
  · have hpd := (prime_dvd_card_psl_two hpf.1 (by omega) hp).trans hdvd
    exact absurd hpf (not_fermatOrMersenne (prime_dvd_small hpf.1 hp7 hN hpd))

end A312Sub
end CFSG.QuasithinUnique.Unc25G2
end
