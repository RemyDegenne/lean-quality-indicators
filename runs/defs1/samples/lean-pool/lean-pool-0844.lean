@[expose] public section

open Finset

namespace Utilities

variable {H : CFGraph}

/-- The junction class `ξ_m = [C + m•α - (y)]` of the pair `m | m+1`. -/
def junction (C : CFDiv H) (x y : H.V) (m : ℤ) : CFDiv H :=
  seamTwist C x y m - oneChip y

end Utilities
end
