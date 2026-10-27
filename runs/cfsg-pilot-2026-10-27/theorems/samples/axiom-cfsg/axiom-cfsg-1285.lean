public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228InspProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

open CFSG.LieType.Universal.Unitary (SU)

open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.RankThreeEven (projSU)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

open CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof (K16 card_K16 σ16 SU54 U54 qU
  isCentralPQuot_qU tt tt_mem exists_tt tt_mul projSUEquivU54 tt4 tt_eq_su4Emb
  qU_su4Emb_injective)

open CFSG.RankThree.PartOne.KFU (torus6 torus6_pow_eq_one exists_conj_into_d8Tor_su d8Comb_five
  IsCentralPQuot exists_toral_quot card_center_mulEquiv)

open CFSG.RankThree.PartOne.K1320X (su4Emb)

open CFSG.RankThree.PartTwo.Sec21.U4Lines (mapL embedOf mapL_le mapL_mono card_mapL mapL_inj
  mapL_perfectResidual mapL_perfectResidual_inf mapL_inf_centralizer perfectResidualEquiv
  embedOf_injective)

theorem exists_model_U54_E9 {G : Type} [Group G] [Finite G] {X T : Subgroup G}
    (eX : X ≃* projSU 5 2 2) (hTX : T ≤ X) (hTe : IsElemAbelian 3 T) (hT9 : Nat.card T = 3 ^ 2) :
    ∃ ε : X ≃* U54, (∀ t ∈ torus6 σ16 3, ((ε.symm (qU t) : X) : G) ∈ T) ∧
      ∀ f (hf : f ∈ T), ∃ t ∈ torus6 σ16 3, ε ⟨f, hTX hf⟩ = qU t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZc : Subgroup.center X = ⊥ := by
    have h := card_center_mulEquiv eX
    rw [Sec4.Item434SmallTwoOther.U54.center_U54, Subgroup.card_bot] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  have h27 : ¬ 27 ∣ Nat.card X := by
    rw [Nat.card_congr eX.toEquiv]
    exact not_twentySeven_dvd_card_projSU_five_four
  set eU : X ≃* U54 := eX.trans projSUEquivU54 with heU
  have hε₀ : IsCentralPQuot 3 eU.toMonoidHom := by
    refine ⟨eU.surjective, ?_, ?_⟩
    · intro x hx
      rw [(MonoidHom.ker_eq_bot_iff _).mpr eU.injective] at hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact Subgroup.one_mem _
    · rw [(MonoidHom.ker_eq_bot_iff _).mpr eU.injective, Subgroup.card_bot]
      norm_num
  have hTcomm : ∀ s ∈ torus6 σ16 3, ∀ t ∈ torus6 σ16 3, s * t = t * s := by
    intro s hs t ht
    obtain ⟨a, b, rfl⟩ := exists_tt hs
    obtain ⟨c, d, rfl⟩ := exists_tt ht
    rw [tt_mul, tt_mul, mul_comm a, mul_comm b]
  have hDiag : ∀ Z : Subgroup SU54, (∀ x ∈ Z, x ^ 3 = 1) →
      (∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) → ∃ g : SU54, ∀ x ∈ Z, g * x * g⁻¹ ∈ torus6 σ16 3 :=
    fun Z hexp _ => exists_conj_into_d8Tor_su (n := 5) (Or.inr rfl) d8Comb_five card_K16
      Nat.prime_three (by norm_num) (by norm_num) Z hexp
  have hFexp : ∀ f ∈ T, f ^ 3 = 1 := fun f hf => hTe.2 f hf
  have hFcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hTe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hmax : ∀ F' : Subgroup G, F' ≤ X → (∀ x ∈ F', x ^ 3 = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → T ≤ F' → F' = T := by
    intro F' hF'X hF'e _ hle
    have hp : IsPGroup 3 F' := fun x => ⟨1, Subtype.ext (by simpa using hF'e x x.2)⟩
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hdvd : 3 ^ k ∣ Nat.card X := hk ▸ Subgroup.card_dvd_of_le hF'X
    have hk2 : k ≤ 2 := by
      by_contra h
      exact h27 ((pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd)
    have hle9 : Nat.card F' ≤ 3 ^ 2 := by
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) hk2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hT9]; exact hle9)).symm
  obtain ⟨ε, hε, hT1, hT2⟩ := exists_toral_quot qU isCentralPQuot_qU eU.toMonoidHom hε₀
    (fun t ht => torus6_pow_eq_one ht) hTcomm hDiag hTX hFexp hFcomm hmax
  have hinj : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have := hε.central hx
    rw [hZc] at this
    exact this
  set ε' : X ≃* U54 := MulEquiv.ofBijective ε ⟨hinj, hε.surjective⟩ with hε'
  refine ⟨ε', ?_, ?_⟩
  · intro t ht
    obtain ⟨f, hf⟩ := hT1 t ht
    have h1 : ε'.symm (qU t) = Subgroup.inclusion hTX f := by
      rw [MulEquiv.symm_apply_eq]
      exact hf.symm
    rw [h1]
    exact f.2
  · intro f hf
    obtain ⟨t, ht, h⟩ := hT2 ⟨f, hf⟩
    exact ⟨t, ht, h⟩

end CFSG.RankThree.PartTwo.Sec21.Item228InspProof
end
