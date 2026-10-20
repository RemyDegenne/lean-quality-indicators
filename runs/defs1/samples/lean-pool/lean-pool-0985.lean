@[expose] public section

namespace Utilities.Certificate.DegenerateSpec.DegSpec

open Utilities.Certificate

open Utilities

open Finset

variable {n p n' p' : ℕ} (source : DegSpec n p) (target : DegSpec n' p')

variable (r : Relabeling source target)

namespace Relabeling

/-- The unit-step occurrence equivalence induced by a closed-face relabeling. -/
def stepEquiv : source.Step ≃ target.Step :=
  Equiv.sigmaCongr r.slotEquiv (fun e =>
    stepOffsetEquiv source target r e)

end Relabeling
end Utilities.Certificate.DegenerateSpec.DegSpec
end
