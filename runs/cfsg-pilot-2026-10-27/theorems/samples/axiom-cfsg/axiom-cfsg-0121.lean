public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_1_2_7_three (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {T L : Subgroup G} (hT : quasithinIsSylowTwo T) (hL : quasithinIsMaximalLocal T L) :
    IsUniqueM (L ⊔ T) (Subgroup.normalizer (conjClosure L T : Set G)) := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hH₀ : pCoreOf 2 (L ⊔ (S : Subgroup G)) ≠ ⊥ := hL.1.2.2.2
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hH₀
  have hnorm : ∀ M : Subgroup G, InM (L ⊔ (S : Subgroup G)) M →
      M ≤ Subgroup.normalizer (conjClosure L (S : Subgroup G) : Set G) := by
    intro M hM
    have hMH : InH (L ⊔ (S : Subgroup G)) M := inH_of_inM hM
    have hTM : (S : Subgroup G) ≤ M := le_sup_right.trans hM.2
    have hLM := lemma_1_2_7_one hK hs hnab h37 h39 hT hL hMH
    exact normal_conjClosure_of_pCoreOf_ne_bot hK hs hnab h37 h38 hMH.2
      (isSylowTwoOf_of_quasithinIsSylowTwo hT hTM) hLM
  have hL₀M : conjClosure L (S : Subgroup G) ≤ M' :=
    conjClosure_le fun h hh z hz =>
      M'.mul_mem (M'.mul_mem (le_sup_right.trans hM'.2 hh) (le_sup_left.trans hM'.2 hz))
        (M'.inv_mem (le_sup_right.trans hM'.2 hh))
  have hL₀ne : conjClosure L (S : Subgroup G) ≠ ⊥ := by
    intro h
    apply ne_bot_of_mem_cComp (cComp_of_isLocal hL.1 : L ∈ cComp (L ⊔ (S : Subgroup G)))
    exact le_bot_iff.mp ((le_conjClosure L (S : Subgroup G)).trans h.le)
  have hSM' : InM (S : Subgroup G) M' := ⟨hM'.1, le_sup_right.trans hM'.2⟩
  have hFM' : CharTwo M' := charTwo_of_inH hK.2.1 S (inH_of_inM hSM')
  have hFL₀ : CharTwo (conjClosure L (S : Subgroup G)) :=
    A4.charTwo_of_subnormal (A3.subnormal_of_normal hL₀M
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL₀M |>.mpr (hnorm M' hM'))) hFM'
  have hO₂ := pCoreOf_ne_bot_of_charTwo hFL₀ hL₀ne
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (conjClosure L (S : Subgroup G)) : Set G)) :=
    ⟨_, hO₂, pCoreOf_isPGroup 2 _, rfl⟩
  have hM'le : M' ≤ Subgroup.normalizer (conjClosure L (S : Subgroup G) : Set G) := hnorm M' hM'
  have hle2 : Subgroup.normalizer (conjClosure L (S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (conjClosure L (S : Subgroup G)) : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 _
  have hM'eq : M' = Subgroup.normalizer (conjClosure L (S : Subgroup G) : Set G) := by
    have h1 := hM'.1.2 _ hloc (hM'le.trans hle2)
    exact le_antisymm hM'le (hle2.trans h1.le)
  refine ⟨⟨hM'eq ▸ hM'.1, hM'.2.trans hM'le⟩, fun M hM => ?_⟩
  have h1 : M ≤ M' := (hnorm M hM).trans hM'eq.ge
  exact hM.1.2 M' hM'.1.1 h1 |>.symm.trans hM'eq

end CFSG.Quasithin
end
