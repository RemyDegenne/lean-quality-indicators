@[expose] public section

noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

@[simp]
theorem arsinh_pos_iff : 0 < arsinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arsinh_nonpos_iff

end Real
end
end
