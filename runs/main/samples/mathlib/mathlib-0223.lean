@[expose] public section

noncomputable section

open Set Filter

open scoped Topology

namespace Real

variable {x y : ℝ}

@[continuity]
theorem continuous_tan : Continuous fun x : {x | cos x ≠ 0} => tan x :=
  continuousOn_iff_continuous_domRestrict.1 continuousOn_tan

end Real
end
end
