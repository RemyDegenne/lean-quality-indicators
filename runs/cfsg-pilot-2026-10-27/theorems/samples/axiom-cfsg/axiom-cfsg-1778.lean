public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Layer

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.T8 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.Q3T7 CFSG.ClassicalInvolution.Q3.Disc3
  CFSG.ClassicalInvolution.Uniform

open scoped commutatorElement

section Img

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_oddCore_conj_of_layerImg3_eq (L : LayerHyp Ω x) {K J : Subgroup G}
    (hK : K ∈ tqMembers3 Ω x) (hJ : J ∈ tqMembers3 Ω x)
    (h : layerImg3 Ω x K = layerImg3 Ω x J) :
    ∃ n ∈ oddCoreOf (exactLayer3 Ω x), conjSub n K = J := by
  have hodd := odd_natCard_oddCore_exactLayer3 (Ω := Ω) (x := x)
  obtain ⟨m, hm, hJ'⟩ := T3CII.exists_conj_of_map_eq_gen L.pair hodd (subgroupOf_mem_exactPair3 hK)
    (subgroupOf_mem_exactPair3 hJ) h
  have hmy : ((m : ↥(exactLayer3 Ω x)) : G) ∈ exactLayer3 Ω x := m.2
  have hmc : ((m : ↥(exactLayer3 Ω x)) : G) ∈ cenZ x := exactLayer3_le_cenZ Ω x hmy
  have hmc' : ((m : ↥(exactLayer3 Ω x)) : G) ∈ Subgroup.centralizer ({x} : Set G) :=
    (cenZ_eq_centralizer x) ▸ hmc
  refine ⟨(m : G), ⟨m, hm, rfl⟩, ?_⟩
  rw [conjSub_subgroupOf] at hJ'
  have h2 := Subgroup.subgroupOf_inj.mp hJ'
  rw [inf_eq_left.mpr (exactCore3_le_exactLayer3 hJ)] at h2
  have hKm : conjSub (m : G) K ∈ tqMembers3 Ω x :=
    conjSub_mem_tqMembers3 L.gen.conjInvariant hmc' hK
  have h3 : conjSub (m : G) (exactCore3 x K) ≤ exactLayer3 Ω x := by
    rw [exactCore3_conj_cen hmc K]
    exact exactCore3_le_exactLayer3 hKm
  rw [inf_eq_left.mpr h3] at h2
  exact eq_of_exactCore3_eq L hKm hJ ((exactCore3_conj_cen hmc K).symm.trans h2.symm)

end Img
end CFSG.ClassicalInvolution.Q3.Q3T8.Layer
end
