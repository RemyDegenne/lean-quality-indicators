public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix

namespace SpChain

variable {K : Type} [Field K]

theorem ext_plk {x y : wedgeSpace K} (h01 : plk 0 1 x = plk 0 1 y) (h02 : plk 0 2 x = plk 0 2 y)
    (h03 : plk 0 3 x = plk 0 3 y) (h12 : plk 1 2 x = plk 1 2 y) (h13 : plk 1 3 x = plk 1 3 y)
    (h23 : plk 2 3 x = plk 2 3 y) : x = y := by
  rw [eq_sum_plk x, eq_sum_plk y, h01, h02, h03, h12, h13, h23]

end SpChain
end CFSG.ComponentClassification.UnbalancedCatalog
end
