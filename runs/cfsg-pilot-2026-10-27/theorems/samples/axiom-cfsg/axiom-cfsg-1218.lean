public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section HeRow

theorem sporadic_rows_he {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .He)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        SporadicInnerRow .He (Nat.card (D ⧸ center D))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        SporadicOuterRow .He (Nat.card (D ⧸ center D))) := by
  refine ⟨fun hin => inner_row_of_centralizer hS hna hσ hD hin
      (P := fun c => c = 20160) (fun u hu B hB => ?_), fun hout => ?_⟩
  · have h := Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order
      ⟨e⟩ hu (isComponentOf_map_centralizer hB)
    rwa [card_quotient_center_map_centralizer] at h
  · have h1 := SeitzReduction.SporadicRefine.he_outer_card_fixedSubgroup e hσ hout
    have h2 := SeitzReduction.SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D
    rwa [h1] at h2

end HeRow
end CFSG.ComponentClassification.CatFC
end
