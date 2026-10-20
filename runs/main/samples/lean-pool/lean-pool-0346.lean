@[expose] public section

namespace LeanPool.PoincareThreeBody

lemma hasDerivAt_inverseSqrt_comp {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) (hpositive : 0 < f x) :
    HasDerivAt (fun y ↦ 1 / Real.sqrt (f y))
      (-(f' / (2 * Real.sqrt (f x))) / (Real.sqrt (f x)) ^ 2) x := by
  have hsqrt := hf.sqrt hpositive.ne'
  have hinv := hsqrt.inv (Real.sqrt_ne_zero'.mpr hpositive)
  apply hinv.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [one_div]

end LeanPool.PoincareThreeBody
end
