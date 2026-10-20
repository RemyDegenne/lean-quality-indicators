open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci

variable {K : Type v} [Field K]

/-- The class `rv_J(b)` of FLLM24, Definition 2.15: the initial form of `b` in Berarducci's
ring `P̂` for the ordinal-value degree `deg_J`, which is zero exactly on `J`. -/
def rvJ (b : Series K) : PrincipalSubring K :=
  (ordinalValueDegreeValuation K).initialForm b

end FLLM24
end
