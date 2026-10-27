@[expose] public section

namespace Utilities.Gonality

open Finset

variable {G : CFGraph}

namespace RankZeroCertificate

variable {D : CFDiv G} (c : RankZeroCertificate G D)

/-- Everything the certificate must satisfy, as one decidable proposition. -/
def Valid : Prop :=
  qEffective c.vertex c.reduced ∧
    BurningOrder G c.reduced c.vertex c.order ∧
    c.reduced c.vertex ≤ 0

end RankZeroCertificate
end Utilities.Gonality
end
