@[expose] public section

open scoped BigOperators

open scoped FinsetFamily

open Finset

namespace BooleanIsoperimetry

lemma slice0_simplicialInitSeg_eq_cascadeSplit {N x p q : ℕ} (h : CascadeSplit N x p q) :
    slice0 (simplicialInitSeg (N + 1) x) = simplicialInitSeg N p := by
  rw [slice0_initSeg_eq, (slice_card_eq_cascade h).1]

end BooleanIsoperimetry
end
