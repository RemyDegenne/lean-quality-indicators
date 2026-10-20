namespace P2MW.S_AlgebraicCurve_exists_constantFieldDescent_finset

attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

open Polynomial IntermediateField Cardinal

universe u v

namespace W7XDesc

theorem core (K : Type u) (F : Type v) [Field K] [Field F]
    [Algebra K F] [IsAlgClosed K] [CharZero K]
    {x : F} (hx : Transcendental K x) (hfin : FiniteDimensional K⟮x⟯ F) (t : Finset F) :
    ∃ (K₀ : Type u) (F₀ : Type v) (_ : Field K₀) (_ : Field F₀)
      (_ : Algebra K₀ F₀) (_ : Algebra K₀ K) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : Algebra K₀ ℂ)
      (_ : IsAlgClosed K₀) (_ : Countable K₀) (_ : CharZero K₀),
      (∃ x₀ : F₀, Transcendental K₀ x₀ ∧ FiniteDimensional K₀⟮x₀⟯ F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ ∧
      (↑t : Set F) ⊆ Set.range (algebraMap F₀ F) := by
  classical

  haveI := hfin
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : PerfectField K⟮x⟯ := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable K⟮x⟯ F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨y, hy⟩ := Field.exists_primitive_element K⟮x⟯ F
  have hxy : K⟮x, y⟯ = ⊤ := by
    rw [← adjoin_simple_adjoin_simple, hy, restrictScalars_top]

  obtain ⟨q, hq0, hqy⟩ : IsAlgebraic K⟮x⟯ y := Algebra.IsAlgebraic.isAlgebraic y
  have hcoef : ∀ j, ∃ r s : K[X], (q.coeff j : F) = aeval x r / aeval x s := fun j =>
    (mem_adjoin_simple_iff (F := K) _).1 (q.coeff j).2
  choose r s hrs using hcoef
  set J := q.support with hJ
  have hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0 := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at hqy
    simp_rw [← hrs]
    exact hqy
  have hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0 := by
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.2 hq0
    refine ⟨j, hj, ?_⟩
    rw [← hrs]
    exact fun h => (mem_support_iff.1 hj) (ZeroMemClass.coe_eq_zero.1 h)

  have hrepr : ∀ z : F, ∃ P Q : K⟮x⟯[X], z = aeval y P / aeval y Q := fun z =>
    (mem_adjoin_simple_iff (F := K⟮x⟯) _).1 (by rw [hy]; exact mem_top)
  choose P Q hPQ using hrepr
  have hcoefP : ∀ z i, ∃ r s : K[X], ((P z).coeff i : F) = aeval x r / aeval x s :=
    fun z i => (mem_adjoin_simple_iff (F := K) _).1 ((P z).coeff i).2
  have hcoefQ : ∀ z i, ∃ r s : K[X], ((Q z).coeff i : F) = aeval x r / aeval x s :=
    fun z i => (mem_adjoin_simple_iff (F := K) _).1 ((Q z).coeff i).2
  choose rp sp hrsp using hcoefP
  choose rq sq hrsq using hcoefQ

  let C : Set K :=
    (⋃ j ∈ J, (((r j).coeffs ∪ (s j).coeffs : Finset K) : Set K)) ∪
      ⋃ z ∈ t, ⋃ i ∈ ((P z).support ∪ (Q z).support),
        (((rp z i).coeffs ∪ (sp z i).coeffs ∪ ((rq z i).coeffs ∪ (sq z i).coeffs) :
          Finset K) : Set K)
  have hCfin : C.Finite := by
    refine Set.Finite.union ?_ ?_
    · exact Set.Finite.biUnion J.finite_toSet fun j _ => Finset.finite_toSet _
    · exact Set.Finite.biUnion t.finite_toSet fun z _ =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun i _ => Finset.finite_toSet _
  let L : Subfield K := Subfield.closure C
  let K₀ : IntermediateField L K := algebraicClosure L K
  haveI : IsAlgClosed K₀ := IsAlgClosure.isAlgClosed L
  haveI : Countable L := by
    haveI : Countable C := hCfin.countable.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max C).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  haveI : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Algebra.IsAlgebraic.cardinalMk_le_max L K₀).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  have hCK₀ : C ⊆ Set.range (algebraMap K₀ K) := by
    intro c hc
    exact ⟨⟨c, K₀.algebraMap_mem ⟨c, Subfield.subset_closure hc⟩⟩, rfl⟩

  have hlift : ∀ p : K[X], (p.coeffs : Set K) ⊆ C →
      ∃ p₀ : K₀[X], p₀.map (algebraMap K₀ K) = p := fun p hp =>
    (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 (hp.trans hCK₀))
  have hrC : ∀ j ∈ J, ((r j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_union_left _ (Set.mem_biUnion hj (by simp [hc]))
  have hsC : ∀ j ∈ J, ((s j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_union_left _ (Set.mem_biUnion hj (by simp [hc]))
  have htC : ∀ z ∈ t, ∀ i ∈ (P z).support ∪ (Q z).support,
      ((rp z i).coeffs : Set K) ⊆ C ∧ ((sp z i).coeffs : Set K) ⊆ C ∧
        ((rq z i).coeffs : Set K) ⊆ C ∧ ((sq z i).coeffs : Set K) ⊆ C := by
    intro z hz i hi
    have hsub : (((rp z i).coeffs ∪ (sp z i).coeffs ∪ ((rq z i).coeffs ∪ (sq z i).coeffs) :
        Finset K) : Set K) ⊆ C := by
      intro c hc
      refine Set.mem_union_right _ ?_
      exact Set.mem_biUnion (Finset.mem_coe.2 hz) (Set.mem_biUnion (Finset.mem_coe.2 hi) hc)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro c hc <;> apply hsub <;> simp [hc]
  have hr₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = r j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hrC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  have hs₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = s j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hsC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose r₀ hr₀ using hr₀
  choose s₀ hs₀ using hs₀
  have hrel' : ∑ j ∈ J, (aeval x (r₀ j) / aeval x (s₀ j)) * y ^ j = 0 := by
    rw [← hrel]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj, hs₀ j hj]
  have hne' : ∃ j ∈ J, aeval x (r₀ j) / aeval x (s₀ j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hne
    refine ⟨j, hj, ?_⟩
    rwa [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj,
      hs₀ j hj]

  obtain ⟨x₀, hx₀x, hx₀, hfin₀⟩ :=
    descent_abstract (hx.of_tower_top K₀) J r₀ s₀ hrel' hne'

  have hxM : x ∈ K₀⟮x, y⟯ := subset_adjoin K₀ _ (by simp)
  have hyM : y ∈ K₀⟮x, y⟯ := subset_adjoin K₀ _ (by simp)
  have htM : ∀ z ∈ t, z ∈ K₀⟮x, y⟯ := by
    intro z hz
    rw [hPQ z]
    refine div_mem ?_ ?_
    · exact aeval_mem_of_repr hxM hyM (P z) (rp z) (sp z) (hrsp z)
        (fun i hi => hlift _ (htC z hz i (Finset.mem_union_left _ hi)).1)
        (fun i hi => hlift _ (htC z hz i (Finset.mem_union_left _ hi)).2.1)
    · exact aeval_mem_of_repr hxM hyM (Q z) (rq z) (sq z) (hrsq z)
        (fun i hi => hlift _ (htC z hz i (Finset.mem_union_right _ hi)).2.2.1)
        (fun i hi => hlift _ (htC z hz i (Finset.mem_union_right _ hi)).2.2.2)

  obtain ⟨ψ⟩ := nonempty_ringHom_complex K₀
  refine ⟨K₀, K₀⟮x, y⟯, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ψ.toAlgebra, inferInstance, inferInstance,
    inferInstance, ⟨x₀, hx₀, hfin₀⟩, ?_, ?_⟩
  · rw [eq_top_iff, ← hxy]
    refine adjoin.mono K _ _ ?_
    rintro z (rfl | h)
    · exact ⟨⟨z, hxM⟩, rfl⟩
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨⟨y, hyM⟩, rfl⟩
  · intro z hz
    exact ⟨⟨z, htM z (Finset.mem_coe.1 hz)⟩, rfl⟩

end W7XDesc
end P2MW.S_AlgebraicCurve_exists_constantFieldDescent_finset
