namespace OAI

noncomputable section

open Set MeasureTheory Filter Function InnerProductSpace

open scoped Topology

namespace Brennan

lemma smoothPower_contDiff (q : ℝ) (n : ℕ∞) : ContDiff ℝ n (smoothPower q) :=
  (bracketSq_contDiff n).rpow_const_of_ne (fun z => (bracketSq_pos z).ne')

end Brennan
end
end OAI
