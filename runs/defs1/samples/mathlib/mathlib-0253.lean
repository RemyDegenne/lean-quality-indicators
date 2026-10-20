public section

open scoped ENNReal

variable {α : Type*}

namespace MeasureTheory

open scoped Function

/-- A mixin class saying that elements `μ : F` are outer measures on `α`.

This typeclass is used to unify some API for outer measures and measures. -/
class OuterMeasureClass (F : Type*) (α : outParam Type*) [FunLike F (Set α) ℝ≥0∞] : Prop where
  protected measure_empty (f : F) : f ∅ = 0
  protected measure_mono (f : F) {s t} : s ⊆ t → f s ≤ f t
  protected measure_iUnion_nat_le (f : F) (s : ℕ → Set α) : Pairwise (Disjoint on s) →
    f (⋃ i, s i) ≤ ∑' i, f (s i)

end MeasureTheory
end
