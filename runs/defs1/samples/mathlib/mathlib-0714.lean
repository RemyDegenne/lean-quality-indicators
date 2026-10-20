@[expose] public section

open Filter TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι] {f : Filtration ι m}

section Progressive

variable {β : Type*} {u v : ι → Ω → β}

/-- Progressive process. A sequence of functions `u` is said to be progressive with respect
to a filtration `f` if at each point in time `i`, `u` restricted to `Set.Iic i × Ω` is measurable
with respect to the product `MeasurableSpace` structure where the σ-algebra used for `Ω` is `f i`.
The usual definition uses the interval `[0,i]`, which we replace by `Set.Iic i`. We recover the
usual definition for index types `ℝ≥0` or `ℕ`. -/
def IsProgressive [MeasurableSpace ι] [MeasurableSpace β] (f : Filtration ι m)
    (u : ι → Ω → β) : Prop :=
  ∀ i, Measurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2

end Progressive
end MeasureTheory
end
