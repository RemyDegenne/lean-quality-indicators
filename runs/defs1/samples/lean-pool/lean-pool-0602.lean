@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace GerverSofa

namespace PartE

open LeanCert.Core

open LeanCert.Engine

open PartALeanCert

/-- Numerator of `denominator * reconstructedB`, with no division. -/
def scaledB (phi theta : ℝ) : ℝ :=
  angleNumerator phi theta * (1 + angleDelta phi theta / 2)
    + bBase phi theta * angleDenominator phi theta

end PartE
end GerverSofa
end
end
end
end
end
end
end
end
