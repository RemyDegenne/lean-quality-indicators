public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification Subgroup

theorem ggFixedRealizedInL_of_config {G : Type} [Group G] [Finite G] (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hInn : GGInnerDiagOn Bs L) : GGFixedRealizedInL p Bs L x := by
  rintro t hr - hxE ⟨Jt, hind, hJC, hpc⟩
  obtain ⟨hp, hBsabel, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨hI, hBsB, hDJ⟩ := hcfg
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := hI.1
  have hp2 : p ≠ 2 := hI.2.2.2.2.2.1.2.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hBsabel.2
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hDJ
  obtain ⟨hJL, hLpc, -⟩ := eq_of_le_of_stdSub hI hDJ hpJ
  have hBsL : Bs ≤ normalizer (L : Set G) := GGDichotomy.le_normalizer_of_innerDiagOn hInn
  have hEBs : ggFixG Bs t ≤ Bs := Subgroup.map_subtype_le _
  have hT : CFSG.Open.lBalanceIsPComponent p (centralizer (ggFixG Bs t : Set G)) Jt :=
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p _ Jt hJC).mp hpc
  have hKx : CFSG.Open.lBalanceIsKGroup ↥(centralizer ({x} : Set G)) :=
    lBalanceIsKGroup_of_kProper hI.2.2.1
      (centralizer_singleton_ne_top_of_isSimpleGroup hI.2.1 hx1)
  obtain ⟨n, hnJt, hnN, hn⟩ := hind
  rcases GGDichotomy.dichotomy_core hL hp hcomm hexp hEBs hxE hKx hBsL
      ((largeEvenPComponent_iff_lBalance p _ L).1 hLpc).2 hT with h | h
  · exact Subgroup.subset_closure ⟨n, h hnJt, hnN, hn⟩
  · exfalso
    refine hr.ne_one hp ?_
    have hLC : IsComponentOf L (centralizer ({x} : Set G)) := hS.2.2.2.1
    have hBsY : Bs ≤ centralizer ({x} : Set G) := fun b hb =>
      mem_centralizer_singleton_iff.mpr (hcomm b hb x hxBs)
    have hEY : centralizer (ggFixG Bs t : Set G) ≤ centralizer ({x} : Set G) :=
      centralizer_le (Set.singleton_subset_iff.mpr hxE)
    obtain ⟨y, hy, hyx⟩ := hxE
    have hyx' : y = ⟨x, hxBs⟩ := Subtype.ext hyx
    subst hyx'
    exact ggAut_eq_one_of_commutator_le_primeCore hp2 hBsY hLx (hEY (hJC hnJt)) hcomm hexp
      hLC.2.2 (hpJ.trans (Subgroup.card_dvd_of_le hJL)) hBsL hxBs
      (GGConfig.bstar_inf_centralizer_L ⟨hI, hBsB, hDJ⟩) hn
      (fun l hl => h (Subgroup.commutator_mem_commutator hnJt hl)) (mem_ggFix.mp hy) hr.1

end CFSG.StandardType
end
