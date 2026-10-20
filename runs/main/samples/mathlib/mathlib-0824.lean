@[expose] public section

open Set Filter

open scoped Filter NNReal Topology

@[inherit_doc]
prefix:max "√" => Real.sqrt

open Real

variable {α : Type*}

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {x : α}

namespace Real

variable {ι : Type*} {f g : ι → ℝ}

open Finset

lemma sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, f i * g i ≤ √(∑ i ∈ s, f i ^ 2) * √(∑ i ∈ s, g i ^ 2) :=
  (le_sqrt_of_sq_le <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq <| sqrt_mul
    (sum_nonneg fun _ _ ↦ by positivity) _

end Real
end
