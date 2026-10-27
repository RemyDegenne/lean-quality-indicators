@[expose] public section

open Finset Function

open Combinatorics

namespace DensityHalesJewett

namespace Subspace

variable {η α ι : Type*}

/-- Restrict the variable letters of a subspace along an alphabet embedding. -/
def restrictAlphabet {β : Type*} [Fintype (η → β)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (e : β ↪ α) : Finset (ι → α) :=
  Finset.univ.image fun x ↦ V (e ∘ x)

end Subspace
end DensityHalesJewett
end
