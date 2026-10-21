namespace OAI

noncomputable section

open List Equiv Equiv.Perm

open scoped BigOperators ENNReal

namespace FKCRT.Inventory

attribute [local instance] Classical.propDecidable

lemma core_tsum_by_size (f : List TypedLetter→ℝ≥0∞) :
    (∑' c : Core,f c.val)=
      ∑' m : ℕ,∑ w∈(typedEmptyWords (2*m)).filter CoreWord,f w := by
  rw [← coreSubtypeEquiv.symm.tsum_eq]
  change (∑' c : {w : EmptyTypedWord // CoreWord w.val},f c.val.val)=_
  calc
    _=∑' w : EmptyTypedWord,Set.indicator {w : EmptyTypedWord | CoreWord w.val}
        (fun w => f w.val) w := tsum_subtype _ _
    _=∑' w : EmptyTypedWord,if CoreWord w.val then f w.val else 0 := rfl
    _=∑' m : ℕ,∑ w∈typedEmptyWords (2*m),if CoreWord w then f w else 0 :=
      empty_tsum_by_size (fun w => if CoreWord w then f w else 0)
    _=_ := by
      apply tsum_congr
      intro m
      simp only [Finset.sum_filter]

end FKCRT.Inventory
end
end OAI
