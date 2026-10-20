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

/-- The residue field of a localization away from the radical of a nonzero
principal ideal is canonically equivalent to the residue field of its
principal-adic completion, realized as a valuation subring of the common
completed fraction field. -/
noncomputable def localizedAdicCompletionResidueFieldEquiv
    {a : V} (ha0 : a ≠ 0)
    (hSrad : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] :
    let hS0 : (0 : V) ∉ S := fun h0 ↦
      Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
    let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
    letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hSnzd
    letI : ValuationRing Vₛ := localization_isValuationRing (Vₛ := Vₛ) S hSnzd
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    IsLocalRing.ResidueField Vₛ ≃+*
      IsLocalRing.ResidueField
        (localizedAdicCompletionValuationSubring (Vₛ := Vₛ) (K := K)
          S ha0 hSrad) := by
  have hS0 : (0 : V) ∉ S := by
    intro h0
    exact Set.disjoint_left.1 hSrad h0 (Ideal.zero_mem _)
  let hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
  letI : IsDomain Vₛ := IsLocalization.isDomain_of_le_nonZeroDivisors Vₛ hSnzd
  letI : ValuationRing Vₛ := localization_isValuationRing (Vₛ := Vₛ) S hSnzd
  letI : Algebra Vₛ K := (Localization.mapToFractionRing K S Vₛ hSnzd).toAlgebra
  letI : IsFractionRing Vₛ K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S Vₛ K
  let I : Ideal Vₛ := Ideal.span {algebraMap V Vₛ a}
  have ha0' : algebraMap V Vₛ a ≠ 0 := by
    simpa using (IsLocalization.injective Vₛ hSnzd).ne ha0
  have ha : algebraMap V Vₛ a ∈ IsLocalRing.maximalIdeal Vₛ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro haunit
    rw [IsLocalization.algebraMap_isUnit_iff S] at haunit
    rcases haunit with ⟨m, hmS, ham⟩
    exact (Set.disjoint_left.1 hSrad hmS)
      (Ideal.le_radical ((Ideal.mem_span_singleton).2 ham))
  letI : IsHausdorff I Vₛ := isHausdorff_localization_span_singleton S Vₛ hSrad
  let C := AdicCompletion I Vₛ
  letI : IsDomain C := principalAdicCompletion_isDomain K (algebraMap V Vₛ a) ha0'
  letI : ValuationRing C :=
    principalAdicCompletion_isValuationRing K (algebraMap V Vₛ a) ha0'
  letI : IsLocalHom (algebraMap Vₛ C) :=
    principalAdicCompletion_algebraMap_isLocalHom K (algebraMap V Vₛ a) ha0' ha
  let e₀ : IsLocalRing.ResidueField Vₛ ≃+* IsLocalRing.ResidueField C :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.map (algebraMap Vₛ C))
      (principalAdicCompletion_residueFieldMap_bijective K
        (algebraMap V Vₛ a) ha0' ha)
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  exact e₀.trans (IsLocalRing.ResidueField.mapEquiv
    (localizedAdicCompletionValuationSubringEquiv (Vₛ := Vₛ) (K := K)
      S ha0 hSrad))

end ValuationRing
end
end
