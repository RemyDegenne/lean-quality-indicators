namespace OAI

noncomputable section

open Set Filter Function

open scoped Topology ContDiff

namespace Problem340.ClockPeriodization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in

theorem locallyFinite_translates {P a b : ℝ} (hP : 0 < P) {f : ℝ × E → F}
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    LocallyFinite (fun k : ℤ => support (fun x : ℝ × E =>
      f (x.1 - (k : ℝ) * P, x.2))) := by
  refine ((locallyFinite_clockIntervals hP a b).preimage_continuous continuous_fst).subset ?_
  intro k x hx
  have h := hsupport (x.1 - (k : ℝ) * P, x.2) hx
  change (k : ℝ) * P + a ≤ x.1 ∧ x.1 ≤ (k : ℝ) * P + b
  constructor <;> linarith [h.1, h.2]

end Problem340.ClockPeriodization
end
end OAI
