public section

namespace Algebra.GrothendieckAddGroup.GradedStabilization

open Algebra Algebra.GrothendieckAddGroup

universe uM uA

variable {M : Type uM} [AddCommMonoid M] {A : Type uA} [AddCommMonoid A]

/-- The normalized map from the set-valued direct limit to the completion kernel. -/
@[expose] noncomputable def normalization (d : M →+ A) (u : M) :
    DirectLimit (degreeFiber d u) (transition d u) → (inducedDegree d).ker :=
  DirectLimit.lift (transition d u) (normalizedAt d u)
    (normalizedAt_transition d u)

end Algebra.GrothendieckAddGroup.GradedStabilization
end
