@[expose] public section

namespace OneMfld

open Set

variable
  {M : Type*}
  [TopologicalSpace M]
  [ConnectedSpace M]
  [T2Space M]

section OverlapHelpers

lemma lt_div_self_of_lt_one {μ ρ : NNReal} (hμ0 : 0 < μ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    μ < μ / ρ := by
  rw [lt_div_iff₀ hρ0]
  exact mul_lt_of_lt_one_right hμ0 hρ1

end OverlapHelpers
end OneMfld
end
