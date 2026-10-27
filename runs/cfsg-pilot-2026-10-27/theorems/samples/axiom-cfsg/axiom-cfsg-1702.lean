public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.SeitzReduction.LinearPilot (SLmEvenTypeDetAt SLmCatalogueClausesAt)

theorem NeighbourOvergroupSL.field {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y))) {m f : ℕ} (hm : 3 ≤ m)
    (hmf : 5 ≤ m ∨ 2 ≤ f) (hdet : SLmEvenTypeDetAt m) (hDm : LieModel D .PSL m 2 f)
    (h : NeighbourOvergroupSL s D m f) : NeighbourOvergroupSLField s D m f := by
  obtain ⟨Kc, hKc, hDKK, ⟨hKt, hDK, hsK, hsN, hov⟩ | hswap⟩ := h
  · obtain ⟨hZ, hmodel⟩ := lieModel_of_slmOvergroup_of_pPrimeCore_eq_bot hO hKc hov hmf
    have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
    have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
    have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
      (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
        ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
    have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK.le
    obtain ⟨hD'c, hD'm, -⟩ := isComponent_fixedSubgroup_of_le hsN hDK.le hDs hDcomp hDm
    have hτ2 : orderOf (Kc.normalizerMonoidHom ⟨s, hsN⟩) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime (F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN hs2) fun h1 => ?_
      apply hov.1
      rw [h1]
      exact one_mem _
    exact ⟨Kc, hKc, hDKK, .inl ⟨hKt, hDK, hsK, hsN, hov.1, hZ, hmodel,
      forall_isPComponent_lieModel_of_not_inner hm hdet hmodel hτ2 hov.1 hD'c hD'm⟩⟩
  · exact ⟨Kc, hKc, hDKK, .inr hswap⟩

end CFSG.SeitzReduction.E6Pilot
end
