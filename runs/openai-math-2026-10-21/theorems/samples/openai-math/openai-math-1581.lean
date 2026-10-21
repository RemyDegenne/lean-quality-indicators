namespace OAI

noncomputable section

open scoped ENNReal

open Filter

namespace HoneycombActual

theorem bridgeProduct_height_sum {bs : List Bridge} {b : Bridge}
    (h : bridgeProduct bs = some b) :
    (b.height : ℝ) = (bs.map (fun a => (a.height : ℝ))).sum := by
  induction bs generalizing b with
  | nil => simp at h
  | cons a as ih =>
    cases he : bridgeProduct as with
    | none =>
      have hn := (bridgeProduct_eq_none_iff _).mp he
      subst as
      have heq : a = b := by simpa using h
      simp [← heq]
    | some c =>
      have heq : a.concat c = b := by simpa [bridgeProduct, he] using h
      rw [← heq]
      simpa using congrArg (fun x : ℝ => (a.height : ℝ) + x) (ih he)

end HoneycombActual
end
end OAI
