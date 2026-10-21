namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset

open scoped ENNReal NNReal BoundedContinuousFunction

open Finset MeasureTheory Filter Topology

open scoped BigOperators

namespace SmoothObstruction.GoodStationary

open MeasureTheory Finset Filter Topology

open SmoothObstruction.DyadicChord

open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Compact

variable [TopologicalSpace Ω]

variable [CompactSpace Ω] [BorelSpace Ω] [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω] in
lemma subinterval_chord {d : ℕ} {T : Ω → Ω} {f : Fin d → Ω → ℝ}
    {k : ℕ} {b : ℝ} {x : Ω} (hx : x ∈ Good T f k b)
    (j : Fin d) {u v : ℕ} (huv : u ≤ v) (hv : v ≤ 2^(k + 1)) :
    |prefixSum (orbit T (f j) x) v - prefixSum (orbit T (f j) x) u -
      (v - u : ℕ) * average (orbit T (f j) x) (2^(k + 1))| ≤ 2 * b * (2 : ℝ)^k := by
  have heq : prefixSum (orbit T (f j) x) v - prefixSum (orbit T (f j) x) u -
      (v - u : ℕ) * average (orbit T (f j) x) (2^(k + 1)) =
      chord (orbit T (f j) x) (2^(k + 1)) v - chord (orbit T (f j) x) (2^(k + 1)) u := by
    rw [Nat.cast_sub huv]
    dsimp [chord]
    ring
  rw [heq]
  calc
    _ ≤ |chord (orbit T (f j) x) (2^(k + 1)) v| +
        |chord (orbit T (f j) x) (2^(k + 1)) u| := abs_sub _ _
    _ ≤ _ := by linarith [hx j v hv, hx j u (huv.trans hv)]

end Compact
end SmoothObstruction.GoodStationary
end
end OAI
