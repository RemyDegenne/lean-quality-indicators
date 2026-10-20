@[expose] public section

open ProbabilityTheory Finset Filter Preorder MeasurableEquiv

open scoped ENNReal Topology

namespace MeasureTheory

section Nat

open Kernel

variable {X : ℕ → Type*}

variable {mX : ∀ n, MeasurableSpace (X n)}
  (μ : (n : ℕ) → Measure (X n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]

namespace Measure

/-- Infinite product measure indexed by `ℕ`. This is an auxiliary construction, you should use
the generic product measure `Measure.infinitePi`. -/
noncomputable def infinitePiNat : Measure (Π n, X n) :=
  (traj (fun n ↦ const _ (μ (n + 1))) 0) ∘ₘ (Measure.pi (fun i : Iic 0 ↦ μ i))

end Measure
end Nat
end MeasureTheory
end
