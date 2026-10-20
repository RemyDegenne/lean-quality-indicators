namespace P2MW.S_AlgebraicCurve_exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_prod_evalAt_param_zpow_eq_one_add_of_semistableModel

attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve IsLocalRing

universe u v w u₁ u₂

namespace C4NCommon

section Core

variable {L : Type u} [Field L] {A : ValuationSubring L} {F : Type v} [Field F] [Algebra L F]
  {ιV : Type u₁} {ιE : Type u₂} {Fbar : ιV → Type w} [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
  {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
  {xs : ∀ e, Place (ResidueField A) (Fbar (src e))} {xt : ∀ e, Place (ResidueField A) (Fbar (tgt e))}
  (M : SemistableModel A F Fbar C An src tgt xs xt)

theorem ord_param_sub_eval [HasPrincipalDivisors L F] (i : ιV) (Q : Place (ResidueField A) (Fbar i))
    (hQ : Q ∉ (C i).nodes)
    (T : F) (hT : T ∈ (C i).integers) (hT0 : (C i).residue ⟨T, hT⟩ ≠ 0) (hT1 : Q.ord ((C i).residue ⟨T, hT⟩) = 1)
    (hTdisc : ∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
      ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ maximalIdeal A)
    (P P' : Place L F) (hP : P ∈ (C i).dom) (hPQ : (C i).placeMap P = Q) (hPrat : P.IsRational)
    (hP' : P' ∈ (C i).dom) (hP'Q : (C i).placeMap P' = Q) :
    (P' = P → P'.ord (T - algebraMap L F (P.evalAt T)) = 1) ∧
      (P' ≠ P → P'.ord (T - algebraMap L F (P.evalAt T)) = 0) := by
  classical
  set c : L := P.evalAt T with hc
  set f : F := T - algebraMap L F c with hfdef

  obtain ⟨hfI, hfres⟩ := sub_eval_mem_integers (C := C) i T hT P ((hTdisc P hP hPQ).2)
  have hfres0 : (C i).residue ⟨f, hfI⟩ ≠ 0 := by rw [hfres]; exact hT0

  have hfmem : ∀ w ∈ (C i).dom, (C i).placeMap w = Q → f ∈ w.toValuationSubring := by
    intro w hw hwQ
    exact w.toValuationSubring.toSubring.sub_mem (hTdisc w hw hwQ).1 (w.algebraMap_mem' c)

  have hf0 : f ≠ 0 := by
    intro h
    apply hfres0
    have : (⟨f, hfI⟩ : (C i).integers) = 0 := Subtype.ext h
    rw [this, map_zero]

  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0
  let D' : Divisor L F := D.filter (fun v => v ∈ (C i).dom)
  have hD'dom : ∀ v ∈ (C i).dom, D' v = v.ord f := by
    intro v hv; simp [D', hv, hD v]
  have hD'off : ∀ v, v ∉ (C i).dom → D' v = 0 := by
    intro v hv; simp [D', hv]

  have key := (C i).mapDomain_placeMap ⟨f, hfI⟩ hfres0 D' hD'dom hD'off Q hQ
  rw [hfres, hT1] at key

  have hsum : (Finsupp.mapDomain (C i).placeMap D') Q =
      ∑ v ∈ D'.support, (if (C i).placeMap v = Q then D' v else 0) := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [Finsupp.single_apply]
  rw [hsum] at key

  have hnonneg : ∀ v ∈ D'.support, 0 ≤ (if (C i).placeMap v = Q then D' v else 0) := by
    intro v hv
    split_ifs with hvQ
    · have hvdom : v ∈ (C i).dom := by
        by_contra h; exact (Finsupp.mem_support_iff.mp hv) (hD'off v h)
      rw [hD'dom v hvdom]
      exact AlgebraicCurve.Place.ord_nonneg_of_mem v (hfmem v hvdom hvQ)
    · exact le_rfl

  have hordP : 1 ≤ P.ord f := by
    have hfP : f ∈ P.toValuationSubring := hfmem P hP hPQ
    have hres : IsLocalRing.residue P.toValuationSubring ⟨f, hfP⟩ = 0 := by
      have hTP : T ∈ P.toValuationSubring := (hTdisc P hP hPQ).1
      have e1 := P.algebraMap_evalAt hPrat hTP
      have : (⟨f, hfP⟩ : P.toValuationSubring) = ⟨T, hTP⟩ - algebraMap L P.toValuationSubring c := by
        apply Subtype.ext; simp [hfdef, Place.coe_algebraMap]
      rw [this, map_sub, ← e1, hc]
      show algebraMap L P.ResidueField (P.evalAt T) -
        IsLocalRing.residue P.toValuationSubring (algebraMap L P.toValuationSubring (P.evalAt T)) = 0
      rw [sub_eq_zero]
      rfl
    have h2 : 0 < P.ord f := ord_pos_of_residue_eq_zero P ⟨f, hfP⟩ hf0 hres
    omega
  have hPsupp : P ∈ D'.support := by
    rw [Finsupp.mem_support_iff, hD'dom P hP]; omega

  have hsplit := Finset.add_sum_erase D'.support (fun v => if (C i).placeMap v = Q then D' v else 0) hPsupp
  rw [← hsplit] at key
  simp only [hPQ, if_true] at key
  rw [hD'dom P hP] at key
  have hrest_nonneg : 0 ≤ ∑ v ∈ D'.support.erase P, (if (C i).placeMap v = Q then D' v else 0) :=
    Finset.sum_nonneg (fun v hv => hnonneg v (Finset.mem_of_mem_erase hv))
  have hPord : P.ord f = 1 := by omega
  have hrest0 : ∑ v ∈ D'.support.erase P, (if (C i).placeMap v = Q then D' v else 0) = 0 := by omega
  refine ⟨fun h => by subst h; exact hPord, fun hne => ?_⟩
  by_cases hsup : P' ∈ D'.support
  · have hmem : P' ∈ D'.support.erase P := Finset.mem_erase.mpr ⟨hne, hsup⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun v hv => hnonneg v (Finset.mem_of_mem_erase hv))).mp
      hrest0 P' hmem
    simp only [hP'Q, if_true] at this
    rw [hD'dom P' hP'] at this
    exact this
  · have := Finsupp.notMem_support_iff.mp hsup
    rw [hD'dom P' hP'] at this
    exact this

end Core
end C4NCommon
end P2MW.S_AlgebraicCurve_exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_prod_evalAt_param_zpow_eq_one_add_of_semistableModel
