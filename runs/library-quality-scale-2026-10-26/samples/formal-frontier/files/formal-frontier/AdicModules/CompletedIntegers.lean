/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion
public import AdicModules.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Principal-adic completions and completed valuation integers

This file identifies a separated principal-adic completion of a valuation ring with the
valuation-integer subring of the completion of its fraction field. The construction works for
arbitrary value-group rank and does not assume Noetherianity or discreteness.

## References

The comparison combines `AdicModules.ValuationTopology` with Mathlib's valuation
integers and valued-field uniform completion, using `AbstractCompletion.funext`
for the two-variable density argument. The consulted Laurent-series comparison
and its authors are credited in `docs/CREDITS.md`; its proof is not copied here.
-/

@[expose] public section

set_option linter.style.haveILetI false

open scoped Topology
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

noncomputable section

universe u v

namespace ValuationRing

/-- The valuation-integer subring in the completion of the fraction field of a valuation ring. -/
noncomputable def CompletionIntegers
    (V : Type u) (K : Type v) [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    Subring (UniformSpace.Completion K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  exact Valued.integer (UniformSpace.Completion K)

variable {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

/-- The canonical `V`-algebra structure on the completed valuation integers. -/
noncomputable instance completionIntegersAlgebra : Algebra V (CompletionIntegers V K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  let f : V →+* UniformSpace.Completion K :=
    (algebraMap K (UniformSpace.Completion K)).comp (algebraMap V K)
  exact (f.codRestrict (CompletionIntegers V K) fun x ↦ by
    change Valued.v ((algebraMap V K x : K) : UniformSpace.Completion K) ≤ 1
    rw [Valued.valuedCompletion_apply]
    exact (ValuationRing.mem_integer_iff V K (algebraMap V K x)).2 ⟨x, rfl⟩).toAlgebra

/-- The algebra map from the completed valuation integers to the completed fraction field is
the subring inclusion. -/
@[simp]
theorem algebraMap_completionIntegers_apply (x : CompletionIntegers V K) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    algebraMap (CompletionIntegers V K) (UniformSpace.Completion K) x =
      (x : UniformSpace.Completion K) := rfl

/-- The algebra map to the completed valuation integers is the composite through the fraction
field and its completion. -/
@[simp]
theorem coe_algebraMap_completionIntegers (x : V) :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    ((algebraMap V (CompletionIntegers V K) x : CompletionIntegers V K) :
      UniformSpace.Completion K) =
      algebraMap K (UniformSpace.Completion K) (algebraMap V K x) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  rfl

/-- The valuation ring has dense image in the completed valuation integers. -/
theorem denseRange_algebraMap_completionIntegers :
    DenseRange (algebraMap V (CompletionIntegers V K)) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  rw [DenseRange, Subtype.dense_iff]
  have hsubset := UniformSpace.Completion.denseRange_coe.subset_closure_image_preimage_of_isOpen
    (Valued.isOpen_integer (UniformSpace.Completion K))
  intro z hz
  apply closure_mono _ (hsubset hz)
  rintro y ⟨x, hx, rfl⟩
  change Valued.v ((x : K) : UniformSpace.Completion K) ≤ 1 at hx
  rw [Valued.valuedCompletion_apply] at hx
  obtain ⟨w, hw⟩ := (ValuationRing.mem_integer_iff V K x).1 hx
  refine ⟨algebraMap V (CompletionIntegers V K) w, ⟨w, rfl⟩, ?_⟩
  simp only [coe_algebraMap_completionIntegers, hw,
    UniformSpace.Completion.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply]

/-- The fraction-field embedding of a valuation ring induces the valuation uniformity on the
valuation ring. -/
theorem isUniformInducing_algebraMap_fractionRing :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    letI : Valued V (ValueGroup V K) :=
      Valued.mk' ((valuation V K).comap (algebraMap V K))
    IsUniformInducing (algebraMap V K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : Valued V (ValueGroup V K) :=
    Valued.mk' ((valuation V K).comap (algebraMap V K))
  apply AddMonoidHom.isUniformInducing_of_isInducing
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  apply Filter.HasBasis.ext (Valued.hasBasis_nhds_zero V (ValueGroup V K))
    ((Valued.hasBasis_nhds_zero K (ValueGroup V K)).comap (algebraMap V K))
  · intro γ _
    let νK := valuation V K
    let νV := νK.comap (algebraMap V K)
    have hsurj : Function.Surjective (valuation V K) := Quotient.mk''_surjective
    obtain ⟨x, hx'⟩ := hsurj
      (ValueGroup₀.embedding (f := .ofClass νV) γ.1)
    have hx : νK x = ValueGroup₀.embedding (f := .ofClass νV) γ.1 := hx'
    have hx0 : νK x ≠ 0 := by
      rw [hx]
      exact (map_ne_zero embedding).2 (Units.ne_zero γ)
    have hδ0 : νK.restrict x ≠ 0 := by
      rw [ne_eq, νK.restrict_eq_zero_iff]
      exact hx0
    let δ : (ValueGroup₀ (.ofClass νK))ˣ := Units.mk0 (νK.restrict x) hδ0
    refine ⟨δ, trivial, ?_⟩
    intro b hb
    change νK.restrict (algebraMap V K b) < δ.1 at hb
    change νV.restrict b < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding] at hb ⊢
    simpa [δ, νV, νK, hx] using hb
  · intro γ _
    let νK := valuation V K
    let νV := νK.comap (algebraMap V K)
    by_cases hγ : 1 ≤ embedding γ.1
    · refine ⟨1, trivial, ?_⟩
      intro b hb
      change νV.restrict b < (1 : ValueGroup₀ (.ofClass νV)) at hb
      change νK.restrict (algebraMap V K b) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding] at hb ⊢
      have hb' : νK (algebraMap V K b) < 1 := by
        simpa [νV, νK] using hb
      exact hb'.trans_le hγ
    · have hγle : embedding γ.1 ≤ 1 := (lt_of_not_ge hγ).le
      have hsurj : Function.Surjective (valuation V K) := Quotient.mk''_surjective
      obtain ⟨x, hx'⟩ := hsurj
        (ValueGroup₀.embedding (f := .ofClass νK) γ.1)
      have hx : νK x = ValueGroup₀.embedding (f := .ofClass νK) γ.1 := hx'
      have hxmem : x ∈ νK.integer := by
        change νK x ≤ 1
        simpa [hx] using hγle
      obtain ⟨a, ha⟩ := (ValuationRing.mem_integer_iff V K x).1 hxmem
      have ha0 : νV a ≠ 0 := by
        change νK (algebraMap V K a) ≠ 0
        rw [ha, hx]
        exact (map_ne_zero embedding).2 (Units.ne_zero γ)
      have hδ0 : νV.restrict a ≠ 0 := by
        rw [ne_eq, νV.restrict_eq_zero_iff]
        exact ha0
      let δ : (ValueGroup₀ (.ofClass νV))ˣ := Units.mk0 (νV.restrict a) hδ0
      refine ⟨δ, trivial, ?_⟩
      intro b hb
      change νV.restrict b < δ.1 at hb
      change νK.restrict (algebraMap V K b) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding] at hb ⊢
      simpa [δ, νV, νK, ha, hx] using hb

/-- The fraction-field embedding of a valuation ring is an open embedding for the canonical
valuation topologies. -/
theorem isOpenEmbedding_algebraMap_fractionRing :
    @Topology.IsOpenEmbedding V K
      (Valued.mk' ((valuation V K).comap (algebraMap V K))).toUniformSpace.toTopologicalSpace
      (Valued.mk' (valuation V K)).toUniformSpace.toTopologicalSpace
      (algebraMap V K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : Valued V (ValueGroup V K) :=
    Valued.mk' ((valuation V K).comap (algebraMap V K))
  refine ⟨⟨(isUniformInducing_algebraMap_fractionRing (V := V) (K := K)).isInducing,
    IsFractionRing.injective V K⟩, ?_⟩
  convert (Valued.isClopen_integer K).isOpen using 1
  exact (congrArg (fun S : Subring K ↦ (S : Set K))
    (ValuationRing.range_algebraMap_eq (A := V) (K := K))).symm

/-- The fraction-field embedding of a valuation ring is a closed embedding for the canonical
valuation topologies. -/
theorem isClosedEmbedding_algebraMap_fractionRing :
    @Topology.IsClosedEmbedding V K
      (Valued.mk' ((valuation V K).comap (algebraMap V K))).toUniformSpace.toTopologicalSpace
      (Valued.mk' (valuation V K)).toUniformSpace.toTopologicalSpace
      (algebraMap V K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : Valued V (ValueGroup V K) :=
    Valued.mk' ((valuation V K).comap (algebraMap V K))
  refine ⟨⟨(isUniformInducing_algebraMap_fractionRing (V := V) (K := K)).isInducing,
    IsFractionRing.injective V K⟩, ?_⟩
  convert (Valued.isClopen_integer K).isClosed using 1
  exact (congrArg (fun S : Subring K ↦ (S : Set K))
    (ValuationRing.range_algebraMap_eq (A := V) (K := K))).symm

/-- The completed valuation integers are an abstract completion of the valuation ring. -/
noncomputable def completionIntegersAbstractCompletion :
    letI : Valued V (ValueGroup V K) :=
      Valued.mk' ((valuation V K).comap (algebraMap V K))
    AbstractCompletion V := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : Valued V (ValueGroup V K) :=
    Valued.mk' ((valuation V K).comap (algebraMap V K))
  refine
    { space := CompletionIntegers V K
      coe := algebraMap V (CompletionIntegers V K)
      uniformStruct := inferInstance
      complete := ?_
      separation := inferInstance
      isUniformInducing := ?_
      dense := denseRange_algebraMap_completionIntegers }
  · change CompleteSpace (Valued.integer (UniformSpace.Completion K))
    exact (Valued.isClosed_integer (UniformSpace.Completion K)).completeSpace_coe
  · let hsub : IsUniformInducing
        ((↑) : CompletionIntegers V K → UniformSpace.Completion K) :=
      isUniformInducing_val _
    apply hsub.of_comp_iff.mp
    have hVK : IsUniformInducing (algebraMap V K) :=
      isUniformInducing_algebraMap_fractionRing
    have hcomp : IsUniformInducing
        (fun x : V ↦ ((algebraMap V K x : K) : UniformSpace.Completion K)) :=
      (UniformSpace.Completion.isUniformInducing_coe K).comp hVK
    convert hcomp using 1
    funext x
    exact coe_algebraMap_completionIntegers x

/-- The ring equivalence underlying `principalAdicCompletionEquiv`. -/
noncomputable def principalAdicCompletionRingEquiv
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    AdicCompletion (Ideal.span {a}) V ≃+* CompletionIntegers V K := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : Valued V (ValueGroup V K) :=
    Valued.mk' ((valuation V K).comap (algebraMap V K))
  letI : WithIdeal (AdicCompletion (Ideal.span {a}) V) :=
    ⟨(Ideal.span {a}).map
      (algebraMap V (AdicCompletion (Ideal.span {a}) V))⟩
  let hI := ValuationRing.isAdic_valuationTopology_span_singleton
    (V := V) (K := K) (a := a) ha0
  let hfg : (Ideal.span {a} : Ideal V).FG := Submodule.fg_span_singleton a
  let P : AbstractCompletion V :=
    { space := AdicCompletion (Ideal.span {a}) V
      coe := algebraMap V (AdicCompletion (Ideal.span {a}) V)
      uniformStruct := inferInstance
      complete := (AdicCompletion.abstractCompletion _ hI hfg).complete
      separation := (AdicCompletion.abstractCompletion _ hI hfg).separation
      isUniformInducing := AdicCompletion.isUniformInducing_algebraMap _ hI hfg
      dense := AdicCompletion.denseRange_algebraMap _ hI hfg }
  let Q : AbstractCompletion V :=
    { space := CompletionIntegers V K
      coe := algebraMap V (CompletionIntegers V K)
      uniformStruct := inferInstance
      complete := by
        change CompleteSpace (Valued.integer (UniformSpace.Completion K))
        exact (Valued.isClosed_integer (UniformSpace.Completion K)).completeSpace_coe
      separation := inferInstance
      isUniformInducing :=
        (completionIntegersAbstractCompletion (V := V) (K := K)).isUniformInducing
      dense := denseRange_algebraMap_completionIntegers }
  letI : UniformSpace P.space := P.uniformStruct
  letI : CompleteSpace P.space := P.complete
  letI : T0Space P.space := P.separation
  letI : UniformSpace Q.space := Q.uniformStruct
  letI : CompleteSpace Q.space := Q.complete
  letI : T0Space Q.space := Q.separation
  let e := P.compareEquiv Q
  refine
    { e.toEquiv with
      map_add' := ?_
      map_mul' := ?_ }
  · intro x y
    apply congr_fun (P.funext
      (e.continuous.comp (continuous_id.mul continuous_const))
      (e.continuous.mul continuous_const) fun r ↦ ?_) x
    apply congr_fun (P.funext
      (e.continuous.comp (continuous_const.mul continuous_id))
      (continuous_const.mul e.continuous) fun s ↦ ?_) y
    change e (P.coe r * P.coe s) = e (P.coe r) * e (P.coe s)
    rw [← map_mul]
    change P.compare Q (P.coe (r * s)) =
      P.compare Q (P.coe r) * P.compare Q (P.coe s)
    rw [P.compare_coe Q, P.compare_coe Q, P.compare_coe Q]
    change algebraMap V (CompletionIntegers V K) (r * s) =
      algebraMap V (CompletionIntegers V K) r *
        algebraMap V (CompletionIntegers V K) s
    exact map_mul _ _ _
  · intro x y
    apply congr_fun (P.funext
      (e.continuous.comp (continuous_id.add continuous_const))
      (e.continuous.add continuous_const) fun r ↦ ?_) x
    apply congr_fun (P.funext
      (e.continuous.comp (continuous_const.add continuous_id))
      (continuous_const.add e.continuous) fun s ↦ ?_) y
    change e (P.coe r + P.coe s) = e (P.coe r) + e (P.coe s)
    rw [← map_add]
    change P.compare Q (P.coe (r + s)) =
      P.compare Q (P.coe r) + P.compare Q (P.coe s)
    rw [P.compare_coe Q, P.compare_coe Q, P.compare_coe Q]
    change algebraMap V (CompletionIntegers V K) (r + s) =
      algebraMap V (CompletionIntegers V K) r +
        algebraMap V (CompletionIntegers V K) s
    exact map_add _ _ _

/-- The underlying ring equivalence agrees with the canonical maps from the valuation ring. -/
@[simp]
theorem principalAdicCompletionRingEquiv_algebraMap
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : V) :
    principalAdicCompletionRingEquiv (V := V) (K := K) a ha0
        (algebraMap V (AdicCompletion (Ideal.span {a}) V) x) =
      algebraMap V (CompletionIntegers V K) x := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : Valued V (ValueGroup V K) :=
    Valued.mk' ((valuation V K).comap (algebraMap V K))
  letI : WithIdeal (AdicCompletion (Ideal.span {a}) V) :=
    ⟨(Ideal.span {a}).map
      (algebraMap V (AdicCompletion (Ideal.span {a}) V))⟩
  unfold principalAdicCompletionRingEquiv
  exact AbstractCompletion.compare_coe _ _ x

/-- A separated principal-adic completion of a valuation ring is canonically the
valuation-integer subring of the completion of its fraction field. -/
noncomputable def principalAdicCompletionEquiv
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    AdicCompletion (Ideal.span {a}) V ≃ₐ[V] CompletionIntegers V K :=
  { principalAdicCompletionRingEquiv (V := V) (K := K) a ha0 with
    commutes' := principalAdicCompletionRingEquiv_algebraMap a ha0 }

/-- The principal-adic comparison agrees with the canonical maps from the valuation ring. -/
theorem principalAdicCompletionEquiv_algebraMap
    (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] (x : V) :
    principalAdicCompletionEquiv (V := V) (K := K) a ha0
        (algebraMap V (AdicCompletion (Ideal.span {a}) V) x) =
      algebraMap V (CompletionIntegers V K) x :=
  principalAdicCompletionRingEquiv_algebraMap (V := V) (K := K) a ha0 x

end ValuationRing

section

variable {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  (a : V) (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V]

/-- An inverse comparison equals a canonical principal-adic element exactly when the completed
valuation integer was the corresponding base-ring image. This permits equality tests on either
side of the comparison without unfolding it. -/
public theorem ValuationRing.principalAdicCompletionEquiv_symm_eq_algebraMap_iff
    (z : ValuationRing.CompletionIntegers V K) (x : V) :
    (ValuationRing.principalAdicCompletionEquiv (K := K) a ha0).symm z =
        algebraMap V (AdicCompletion (Ideal.span {a}) V) x ↔
      z = algebraMap V (ValuationRing.CompletionIntegers V K) x := by
  rw [(ValuationRing.principalAdicCompletionEquiv (K := K) a ha0).symm_apply_eq,
    ValuationRing.principalAdicCompletionEquiv_algebraMap (K := K) a ha0 x]

end
