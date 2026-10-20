@[expose] public section

namespace Utilities.Certificate

open Finset

namespace ExplicitPotential.CertificateData

variable {m n p : ℕ}

theorem bnExists_on_subdivision_of_valid
    (certificate : ExplicitPotential.CertificateData m n p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) (degree : ℤ)
    (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hConnected : graphConnected
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph) :
    BNExists
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
      1 degree := by
  apply certificate.bnExists_of_valid_of_strongSeparator point core_nonempty
    degree hValid hCone hConnected
  exact SubdivisionGraph.Spec.coreVertices_strongSeparatorCertificate
    (certificate.subdivisionSpec point core_nonempty hValid hCone)

end ExplicitPotential.CertificateData
end Utilities.Certificate
end
