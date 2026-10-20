@[expose] public section

set_option linter.style.haveILetI false

open scoped Topology

noncomputable section

universe u v w

namespace ValuationRing

variable {V : Type u} {Vₛ : Type v} {K : Type w}
  [CommRing V] [IsDomain V] [ValuationRing V]
  [CommRing Vₛ] [Field K] [Algebra V Vₛ] [Algebra V K]
  (S : Submonoid V) [IsLocalization S Vₛ] [IsFractionRing V K]

/-- The localized principal-adic completion is canonically isomorphic to its
realization as a valuation subring of the common completed fraction field. -/
noncomputable def localizedAdicCompletionValuationSubringEquiv
    {a : V} (ha0 : a ≠ 0)
    (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    AdicCompletion (Ideal.span {algebraMap V Vₛ a}) Vₛ ≃+*
      localizedAdicCompletionValuationSubring (Vₛ := Vₛ) (K := K) S ha0 hSrad := by
  have hS0 : (0 : V) ∉ S := by
    intro h0
    exact Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
  let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
  letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hSnzd
  letI : ValuationRing Vₛ :=
    localization_isValuationRing (Vₛ := Vₛ) S hSnzd
  letI : Algebra Vₛ K := (Localization.mapToFractionRing K S Vₛ hSnzd).toAlgebra
  letI : IsFractionRing Vₛ K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S Vₛ K
  let I : Ideal Vₛ := Ideal.span {algebraMap V Vₛ a}
  have ha0' : algebraMap V Vₛ a ≠ 0 := by
    simpa using (IsLocalization.injective Vₛ hSnzd).ne ha0
  letI : IsHausdorff I Vₛ := isHausdorff_localization_span_singleton S Vₛ hSrad
  letI : IsDomain (AdicCompletion I Vₛ) :=
    principalAdicCompletion_isDomain K (algebraMap V Vₛ a) ha0'
  let hA : ValuationRing (AdicCompletion I Vₛ) :=
    principalAdicCompletion_isValuationRing K (algebraMap V Vₛ a) ha0'
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  letI : ValuationRing (AdicCompletion I Vₛ) := hA
  letI : Algebra (AdicCompletion I Vₛ) (UniformSpace.Completion K) :=
    localizedAdicCompletionFractionFieldAlgebra (K := K) S ha0 hSrad
  letI : IsFractionRing (AdicCompletion I Vₛ) (UniformSpace.Completion K) :=
    localizedAdicCompletion_isFractionRing (K := K) S ha0 hSrad
  exact ValuationRing.equivInteger (AdicCompletion I Vₛ) (UniformSpace.Completion K)

end ValuationRing
end
end
