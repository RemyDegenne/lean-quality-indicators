namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage

open Binary Binary.Automatic Binary.Automatic.Poly

namespace Input

theorem entry_point (C : Input) (x y : C.Point) :
    C.raw.entry (finSumFinEquiv x).val (finSumFinEquiv y).val =
      encodeRat (C.pointDistance x y) := by
  cases x with
  | inl j =>
    cases y with
    | inl l =>
      simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, Raw.entry, raw_m,
        j.isLt, l.isLt, ↓reduceIte, pointDistance, Fin.val_inj]
      split_ifs <;> rfl
    | inr i =>
      have hij : j.val ≠ C.m + i.val := by omega
      have hm : ¬ C.m + i.val < C.m := by omega
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd, Raw.entry, raw_m, raw_n, hij,
        j.isLt, hm, ↓reduceIte, Nat.add_sub_cancel_left, C.table_get, pointDistance]
      split_ifs <;> rfl
  | inr i =>
    cases y with
    | inl j =>
      have hij : C.m + i.val ≠ j.val := by omega
      have hm : ¬ C.m + i.val < C.m := by omega
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd, Raw.entry, raw_m, raw_n, hij,
        j.isLt, hm, ↓reduceIte, Nat.add_sub_cancel_left, C.table_get, pointDistance]
      split_ifs <;> rfl
    | inr h =>
      have hi : ¬ C.m + i.val < C.m := by omega
      have hh : ¬ C.m + h.val < C.m := by omega
      simp only [finSumFinEquiv_apply_right, Fin.val_natAdd, Raw.entry, raw_m,
        hi, hh, ↓reduceIte, Nat.add_left_cancel_iff, Fin.val_inj, pointDistance]
      split_ifs <;> rfl

end Input
end MetricKMedian.Coverage
end Inline_PCPInherited
end OAI
