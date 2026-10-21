namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage

open Finset

namespace ProjectionSystem

variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]

variable (G : ProjectionSystem U V I A B)

omit [DecidableEq V] [DecidableEq I] in
theorem active_budget {d : ℕ} (hreg : G.LeftRegular d)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U) :
    ∑ v, (Partitions.active (G.parts S v)).card ≤ Fintype.card I * Fintype.card V := by
  calc
    _ ≤ ∑ v, ∑ i, (labels S (G.neighbor v i)).card :=
      sum_le_sum (fun v _ => G.active_le S v)
    _ = d * S.card := by rw [G.regular_sum hreg (fun u => (labels S u).card), labels_sum]
    _ ≤ d * Fintype.card U := Nat.mul_le_mul_left d hS
    _ = _ := G.regular_degrees hreg

end ProjectionSystem
end MetricKMedian.Coverage
end Inline_PCPInherited
end OAI
