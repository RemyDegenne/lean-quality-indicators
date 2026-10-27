public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG.CGT.PushingUpLit.SolKNA.R4.ThmE CFSG.ClassicalInvolution.Asc77.Thompson

open scoped commutatorElement

section Cor

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem mem_secD_of_normal (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    {W : Subgroup G} (hW : W ∈ WSet Ω) (huW : u ∈ W)
    {V : Subgroup (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u))}
    (hV : V ∈ WSet (TwinDisc.secFam Ω u)) (hVn : ∀ x, conjSub x V = V) :
    ∀ N ∈ TwinDisc.secFam Ω u, N ∈ secD Ω W u := by
  classical
  obtain ⟨Pb, hlayer⟩ := layer hΩ hc2 hW huW
  have hΦ : HypOmegaGen (TwinDisc.secFam Ω u) := hypOmegaGen_secFam hΩ hc2
  intro N hN
  obtain ⟨η, hη, rfl⟩ := id hV
  have hV2 : IsPGroup 2 ↥(⨆ U ∈ η, U) := isPGroup_of_mem_WSet hV
  haveI : (⨆ U ∈ η, U).Normal := normal_of_conj_eq hVn
  have hVPb : (⨆ U ∈ η, U) ≤ (Pb : Subgroup _) := hV2.le_sylow_of_normal Pb
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (T := ⊥) IsPGroup.of_bot (bot_le : ⊥ ≤ N)
  obtain ⟨S', hS'⟩ := hR.2.1.exists_le_sylow
  have hVS' : ∀ U ∈ η, U ≤ (S' : Subgroup _) := fun U hU =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) U hU).trans (hV2.le_sylow_of_normal S')
  have hmem := member_inf_mem_eta hΦ hη hVS' hN hR hS'
  exact hlayer (mem_USet_of_mem_etaG hη hmem) (inf_le_right.trans hVPb) hN inf_le_left

end Cor
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711
end
