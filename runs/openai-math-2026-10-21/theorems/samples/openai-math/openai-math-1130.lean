namespace OAI

namespace Laughlin.Certificate

theorem computeGram_22_3_17 : GramCompute.ZFast 22 3 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate
end OAI
