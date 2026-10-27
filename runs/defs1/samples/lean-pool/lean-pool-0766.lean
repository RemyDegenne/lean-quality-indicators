@[expose] public section

namespace FD1D.V5.LocalBellman

noncomputable section

open LocalPolicy

namespace Normalized

/-- Weight of the correction term in the floor residual estimate. -/
def floorW (u v K : ℝ) : ℝ :=
  (K + 1) * (u + 1) / (2 * (v + 1))

end Normalized
end
end FD1D.V5.LocalBellman
end
