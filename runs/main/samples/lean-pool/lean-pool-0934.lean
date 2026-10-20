universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Berarducci

open HahnSeries Ordinal

variable {K : Type v} [Field K]

theorem le_ordinalValue_translatedTruncation_of_forall_le_orderType
    (b : K⟦ℝ⟧) (γ : ℝ) {ρ : Ordinal}
    (h : ∀ θ, θ < γ → ρ ≤ (b.isPWO_support.mono
        (s := b.support ∩ Set.Ioo θ γ) Set.inter_subset_left).orderType) :
    NatOrdinal.of ρ ≤ ordinalValue (translatedTruncation b γ) := by
  apply le_ordinalValue_of_forall_mem_representativeOrderTypes
  intro p hp
  obtain ⟨d, hd, rfl⟩ := mem_representativeOrderTypes_iff.mp hp
  rw [NatOrdinal.of.le_iff_le]
  obtain ⟨θ, hθ, hcoeff⟩ := exists_coeff_eq_of_sub_mem_nearConstantSubgroup hd
  set A : Set ℝ := b.support ∩ Set.Ioo (γ + θ) γ with hA
  have hAPWO : A.IsPWO := b.isPWO_support.mono Set.inter_subset_left
  have hmono : StrictMonoOn (fun x ↦ -γ + x) A := fun _ _ _ _ hxy ↦ by simpa using hxy
  have himage : (fun x ↦ -γ + x) '' A ⊆ (d : K⟦ℝ⟧).support := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxsupp, hxlow, hxhigh⟩ := hx
    have hδ0 : -γ + x ≤ 0 := by linarith
    have hδθ : θ < -γ + x := by linarith
    have hδneg : -γ + x < 0 := by linarith
    have hgerm : ((translatedTruncation b γ : Series K) : K⟦ℝ⟧).coeff (-γ + x) = b.coeff x := by
      rw [coeff_translatedTruncation, ite_eq_left hδ0]
      congr 1
      ring
    rw [HahnSeries.mem_support, ← hcoeff (-γ + x) hδθ hδneg, hgerm]
    exact (HahnSeries.mem_support _ _).mp hxsupp
  calc ρ ≤ hAPWO.orderType := h (γ + θ) (by linarith)
    _ = (hAPWO.image_of_monotoneOn hmono.monotoneOn).orderType :=
        (hAPWO.orderType_image_of_strictMonoOn hmono).symm
    _ ≤ (d : K⟦ℝ⟧).isPWO_support.orderType :=
        (hAPWO.image_of_monotoneOn hmono.monotoneOn).orderType_mono _ himage
    _ = (d : K⟦ℝ⟧).supportOrderType :=
        (HahnSeries.supportOrderType_eq_setOrderType _).symm

end Berarducci
end
