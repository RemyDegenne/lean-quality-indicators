namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped MeasureTheory

namespace Invariant233.ConditionalObservationTransport

variable {Ω D Y E : Type*} [mΩ : MeasurableSpace Ω]
  [mD : MeasurableSpace D] [mY : MeasurableSpace Y]
  {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in

theorem aestronglyMeasurable_encoding
    [NormedAddCommGroup E] [CompleteSpace E]
    {X : Ω → D} {encode : D → Y} {decode : Y → D}
    (hdecode : Measurable decode)
    (hrecover : ∀ᵐ ω ∂μ, decode (encode (X ω)) = X ω)
    {g : Ω → E} (hg : StronglyMeasurable[mD.comap X] g) :
    AEStronglyMeasurable[mY.comap (encode ∘ X)] g μ := by
  obtain ⟨k, hk, hkg⟩ := hg.exists_eq_measurable_comp
  have hobs : Measurable[mY.comap (encode ∘ X)] (encode ∘ X) :=
    measurable_iff_comap_le.mpr le_rfl
  refine ⟨k ∘ decode ∘ (encode ∘ X),
    hk.comp_measurable (hdecode.comp hobs), ?_⟩
  filter_upwards [hrecover] with ω hω
  simp only [hkg, Function.comp_apply, hω]

end Invariant233.ConditionalObservationTransport
end
end OAI
