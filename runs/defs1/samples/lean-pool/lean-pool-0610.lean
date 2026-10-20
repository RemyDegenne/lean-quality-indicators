@[expose] public section

namespace BeyondBethe

open Complexity

/-- Subtracts the parallel ellipsoid scale from the perpendicular scale in raw rational
arithmetic. -/
def rawDirectionGap (d : ℕ) : RawRat :=
  (rawEllipsoidPerpScale d).sub (rawEllipsoidParallelScale d)

end BeyondBethe
end
