public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
  {μ : Measure Ω} {X : ℕ × ℕ → Ω → α} {ν : Ω → ProbabilityMeasure (ℕ → α)}

theorem SeparatelyExchangeable.jointLaw_arrayRow_colReindex_eq [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X)
    (hν : ConditionallyIIDWith μ (arrayRow X) ν) (τ : Equiv.Perm ℕ) :
    (μ.map fun ω ↦ ((ν ω).map (fun x : ℕ → α ↦ fun k ↦ x (τ k)),
        fun p : ℕ × ℕ ↦ X (p.1, τ p.2) ω))
      = μ.map fun ω ↦ (ν ω, fun p : ℕ × ℕ ↦ X p ω) :=
  h.jointLaw_arrayRow_pairReindex_eq hν 1 τ

end Probability
end TauCeti
end
end
