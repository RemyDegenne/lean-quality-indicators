public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

namespace IsQuasiFlasque

variable (F : Sheaf AddCommGrpCat.{u} X)

/-- The canonical kernel-envelope-quotient short complex. -/
abbrev flasqueInjectiveEnvelopeShortComplex :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (toFlasqueInjectiveEnvelope F)
    (cokernel.π (toFlasqueInjectiveEnvelope F))
    (cokernel.condition (toFlasqueInjectiveEnvelope F))

end IsQuasiFlasque
end TopCat.Sheaf
end
end
