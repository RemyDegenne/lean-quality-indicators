public section

open scoped unitInterval

open Topology Set

namespace Path

variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace Homotopic.Quotient

theorem subpath_zero_one {x y : X} (p : Path x y) :
    mk (p.subpath 0 1) = (mk p).cast (by simp) (by simp) := by
  simp only [← mk_cast, eq]
  rw [Path.subpath_zero_one]

end Homotopic.Quotient
end Path
end
