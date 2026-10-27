public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem sq_le_relIndex_centralizerMod
    {H U L N : Subgroup G} {q : ℕ}
    (hX : IsSzU3Quot (oTwoQuot ↥H) q) (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    {t : G} (htH : t ∈ H) (ht : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H) :
    q ^ 2 ≤ (centralizerMod L N (Subgroup.zpowers t)).relIndex N := by
  classical
  obtain ⟨hQ, hZinv, hbound⟩ := bender_actor_facts (X := oTwoQuot ↥H) (q := q) hX
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  haveI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr hNL
  have hnotriv : ∃ h ∈ H, ∃ u ∈ N, h * u * h⁻¹ * u⁻¹ ∉ L := by
    by_contra hcon
    apply hnc
    intro h hh u hu
    by_contra hnu
    exact hcon ⟨h, hh, u, hu, hnu⟩
  have hmax : ∀ X : Subgroup G, L ≤ X → X ≤ N →
      H ≤ Subgroup.normalizer (X : Set G) → X = L ∨ X = N := by
    intro X hLX hXN hHX
    exact hstep.2.2.2 X
      ⟨hXN.trans hstep.1.1, fun g hg x hx =>
        (Subgroup.mem_normalizer_iff.mp (hHX hg) x).mp hx⟩ hLX hXN
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) := isElemAbelian_chiefMod hstep hUH hU
  have hQK : pCoreOf 2 H ≤ centralizerMod L H N :=
    Ch3z.pCoreOf_le_centralizerMod hUH hstep hE
  have hO2triv : ∀ r ∈ pCoreOf 2 H, ∀ u ∈ N, r * u * r⁻¹ * u⁻¹ ∈ L :=
    fun r hr u hu => (hQK hr).2.2 u hu
  obtain ⟨hnt, La, tL, hperf, hirr, htL, htL2, htL1, hact, ⟨eCQ⟩, hsq⟩ :=
    section_actor (U := N) (U' := L) (chiefStep_section_sq_mem hU hUH hstep)
      hHN hHL hstep.2.2.1 hmax hnotriv hO2triv hQ hZinv htH ht htO
  have hWcomm : ∀ x y : SectionW N L, x * y = y * x := by
    intro x y
    calc x * y = (x * y)⁻¹ :=
          (inv_eq_of_mul_eq_one_right (hsq (x * y))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
          rw [inv_eq_of_mul_eq_one_right (hsq x), inv_eq_of_mul_eq_one_right (hsq y)]
  letI : CommGroup (SectionW N L) :=
    { (inferInstance : Group (SectionW N L)) with mul_comm := hWcomm }
  haveI : Nontrivial (SectionW N L) := hnt
  let K : Subgroup (SectionW N L) := fixV (Subgroup.zpowers tL)
  have hKmem : ∀ u : ↥N, QuotientGroup.mk u ∈ K ↔
      tL (QuotientGroup.mk u) = QuotientGroup.mk u :=
    fun u => mem_fixV_zpowers_iff_apply
  have hactor : q ^ 2 ≤ (fixV (Subgroup.zpowers tL)).index :=
    hbound (SectionW N L) hsq La hperf hirr ⟨eCQ⟩ tL htL htL2 htL1
  rw [relIndex_centralizerMod_eq_index_of_fixedSection hHN hHL htH hNL tL K hKmem hact]
  exact hactor

end CFSG.Quasithin.Stroth
end
