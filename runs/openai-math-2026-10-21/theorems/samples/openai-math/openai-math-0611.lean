namespace OAI

namespace Laughlin.Certificate

theorem computeGram_19_1_9 : GramCompute.ZFast 19 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate
end OAI
