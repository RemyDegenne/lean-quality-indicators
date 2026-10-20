@[expose] public section

universe u v w

theorem Valuation.Integers.isAdicComplete_span_singleton
    {V : Type u} {K : Type v} {Γ₀ : Type w}
    [CommRing V] [Field K] [Algebra V K]
    [LinearOrderedCommGroupWithZero Γ₀]
    [hv : Valued K Γ₀] [CompleteSpace K]
    (hV : hv.v.Integers V) {a : V}
    [IsHausdorff (Ideal.span {a}) V] :
    IsAdicComplete (Ideal.span {a}) V := by
  by_cases ha : a = 0
  · subst a
    simpa only [Ideal.span_singleton_zero] using (inferInstance : IsAdicComplete (⊥ : Ideal V) V)
  let : IsDomain V := hV.hom_inj.isDomain
  let : ValuationRing V := ValuationRing.of_integers hv.v hV
  let : IsFractionRing V K := hV.isFractionRing
  let ν := ValuationRing.valuation V K
  have heq : ν.IsEquiv hv.v := Valuation.isEquiv_of_val_le_one fun x ↦ by
    change x ∈ ν.integer ↔ hv.v x ≤ 1
    rw [ValuationRing.mem_integer_iff]
    exact ⟨fun ⟨r, hr⟩ ↦ hr ▸ hV.map_le_one r, fun hx ↦ hV.exists_of_le_one hx⟩
  -- Transport completeness before replacing the given valuation by the canonical one.
  have : CompleteSpace (WithVal ν) :=
    (WithVal.uniformEquiv rfl heq).completeSpace_iff.mpr inferInstance
  let : Valued K (ValuationRing.ValueGroup V K) := Valued.mk' ν
  have : CompleteSpace K :=
    (WithVal.uniformEquiv rfl (show ν.IsEquiv ν from .refl)).completeSpace_iff.mp inferInstance
  let : Valued V (ValuationRing.ValueGroup V K) :=
    Valued.mk' (ν.comap (algebraMap V K))
  have hi : IsUniformInducing (algebraMap V K) :=
    ValuationRing.isUniformInducing_algebraMap_fractionRing
  have hrange : IsClosed (Set.range (algebraMap V K)) :=
    (ValuationRing.isClosedEmbedding_algebraMap_fractionRing (V := V) (K := K)).isClosed_range
  have : CompleteSpace V := hi.completeSpace hrange.isComplete
  have : T2Space V := (Topology.IsEmbedding.mk hi.isInducing hV.hom_inj).t2Space
  exact (ValuationRing.isAdic_valuationTopology_span_singleton (K := K) ha).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

end
