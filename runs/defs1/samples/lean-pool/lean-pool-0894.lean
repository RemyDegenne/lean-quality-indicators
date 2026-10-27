@[expose] public section

namespace MarkedGraphs.Certificate

open Utilities.Certificate

open Utilities

open Finset

open ExplicitPotential

open SubdivisionGraph

namespace AffinePosition

namespace SlopeScript

variable {m n p b : ℕ}

/-- Every break position of the script has its bound rows in the local cone. -/
def BoundsCertified (certificate : ExplicitPotential.CertificateData m n p)
    (script : SlopeScript m p b) : Prop :=
  ∀ index : Fin b, (script.entry index).position.BoundsCertified certificate

end SlopeScript
end AffinePosition
end MarkedGraphs.Certificate
end
