namespace OAI

open Set Function Filter MeasureTheory

open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem ae_tag_contacts_singleton_at_independent_level
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hH : ∀ i, IsClosed (d.levels i))
    (Free : Set X) (hP : OrderedLevelNullCompatibility d.levels Free)
    (hunique : ∀ x ∈ Free, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (P : ProbabilityMeasure (BasePathCode d)) (ω : TupleType → ℝ≥0∞)
    [SFinite (tupleReference ω)] (hτ : meanCodeTuple d P ≪ tupleReference ω) (i : ℕ) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ k q, Γ.val.2 k = Sum.inr q → ∀ t,
        tagLeft (Sum.inr q) < t → t < tagRight (Sum.inr q) →
        Γ.val.1 t ∈ Free → (θ, Γ.val.1 t) ∈ d.levels i →
        ¬ (connectedComponentIn {x | (θ, x) ∈ d.levels i} (Γ.val.1 t)).Nontrivial := by
  have hg := ae_active_slots_avoid_independent_null d P (tupleReference ω) volume hτ
    {p | ¬ TuplePairCompatible d.levels Free p.1 (singleLevelTuple i p.2)}
    (tupleReference_single_level_incompatible_null d.levels Free hP ω i)
  filter_upwards [hg] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  intro k q hq t hl hr hx hlevel
  have hcompat : TuplePairCompatible d.levels Free (tagDataTuple q) (singleLevelTuple i θ) :=
    not_not.mp (hθ k q hq)
  exact active_tag_singleton_at_compatible_level d.levels hH Free Γ.val.1 q
    (hq ▸ (Γ.property.1.2.1 k).1) (hq ▸ (Γ.property.1.2.1 k).2.1)
    t hl hr hx (hunique _ hx) i θ hlevel hcompat

end CircleDomainRigidity
end
end OAI
