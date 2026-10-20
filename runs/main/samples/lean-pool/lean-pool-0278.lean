@[expose] public section

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter

open scoped ContDiff ENNReal RealInnerProductSpace

theorem secondKernel_smooth (t : ℝ) (a b : Space) :
    ContDiff ℝ ∞ (secondKernel t a b) := by
  unfold secondKernel
  exact (((contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).mul
    (contDiff_id.inner ℝ contDiff_const)).sub contDiff_const).mul (kernel_smooth t)

end EulerWholeSpaceGaussian
end
end
