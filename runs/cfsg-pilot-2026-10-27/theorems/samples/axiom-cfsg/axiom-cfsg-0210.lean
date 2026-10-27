public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem oddIn_le_center_of_component
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hElem : L34ElementaryCenterSylowFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu2 : orderOf u = 2) (huc : ∀ s ∈ S, s * u = u * s) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hSN : S ≤ normalizer (K₁ : Set G))
    (hrk : ∀ E : Subgroup G, E ≤ S → IsElemTwo E →
      Nat.card E ≤ 8 * Nat.card ↥(E ⊓ coreActionKernel K₁)) :
    ∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨hbase, -, -, hSyl, -, -, -⟩ := hset'
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  obtain ⟨E, hEP, hEl, hEc⟩ := exists_elemTwo_sixtyFour h59 hset
  have hES : E ≤ S := hEP.trans (sup_le inf_le_left ((omegaOne_le _).trans inf_le_left))
  have h8 : 8 ≤ Nat.card ↥(E ⊓ coreActionKernel K₁) := by
    have := hrk E hES hEl
    omega
  obtain ⟨F, hFle, hFc⟩ := exists_le_card_eight ((hS2.to_le hES).to_le inf_le_left) h8
  have hFel : IsElemTwo F := hEl.mono (hFle.trans inf_le_left)
  have hFS : F ≤ S := (hFle.trans inf_le_left).trans hES
  have hWF := wGroup_eq_bot_of_le_sup_omegaOne hS hU hheld hSol hGW h58 hElem hset ⟨hFel, hFc⟩
    ((hFle.trans inf_le_left).trans hEP)
  have hbal : ∀ e ∈ F, e ≠ 1 →
      ⁅(pPrimeCore 2 K₁).map K₁.subtype ⊓ centralizer ({e} : Set G),
        (pLayer ↥(K₁ ⊓ centralizer ({e} : Set G)) 2).map
          (K₁ ⊓ centralizer ({e} : Set G)).subtype⁆ ≤
      (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype :=
    fun e he he1 => commutator_oddCore_pLayer_le hS hU hheld hK hu2 hK₁u hK₁p
      (huc e (hFS he)).symm
      (centralizer_ne_top_of_not_mem_center (not_mem_center_of_ne_one hnonab he1))
  have hcom := oddCore_le_center_of_wGroup_eq_bot hK₁u hK₁p
    (fun e he => mem_centralizer_singleton_iff.mpr (huc e (hFS he))) hFel.1 hFel.2
    (by rw [hFc]; norm_num) (hFS.trans hSN)
    (fun e he => conj_mem_oddIn_of_mem_coreActionKernel (mem_inf.mp (hFle he)).2)
    hWF hbal (Or.inr (by rw [hFc]))
  exact hcom

end CFSG.ComponentClassification.GrSLit.GrS5
end
