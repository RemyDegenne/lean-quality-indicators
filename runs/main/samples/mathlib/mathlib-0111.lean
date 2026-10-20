@[expose] public section

open Finset Real Filter Asymptotics

open scoped Topology

namespace AkraBazziRecurrence

variable {α : Type*} [Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}

variable [Nonempty α] (R : AkraBazziRecurrence T g a b r)

local notation "ε" => smoothingFn

section

include R

lemma one_mem_range_sumCoeffsExp : 1 ∈ Set.range (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  refine mem_range_of_exists_le_of_exists_ge R.continuous_sumCoeffsExp ?le_one ?ge_one
  case le_one =>
    exact R.tendsto_zero_sumCoeffsExp.eventually_le_const zero_lt_one |>.exists
  case ge_one =>
    exact R.tendsto_atTop_sumCoeffsExp.eventually_ge_atTop _ |>.exists

end
end AkraBazziRecurrence
end
