public noncomputable section

universe u v

namespace Multiset

namespace SelectionWeights

variable {α : Type v} (s : SelectionWeights.{u, v} α)

open Classical in
theorem relevantValues_eq_map (w : Multiset α) (hw : w ≠ 0) :
    s.relevantValues w hw = (w.toFinset.filter fun y ↦
      s.weight (s.selected w hw) ≤ s.weight y).val.map fun y ↦ s.weight y :=
  (rfl)

end SelectionWeights
end Multiset
end
