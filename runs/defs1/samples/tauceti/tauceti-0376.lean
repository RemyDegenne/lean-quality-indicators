public section

open scoped BigOperators

namespace TauCeti.NumberField.Chebotarev

open Finset Nat

/-- The elements of a finite group whose order is divisible by `f`.

The carrier is deliberately a `Finset`, so the tags can be indexed by their order. -/
noncomputable def taggedElements {H : Type*} [Group H] [Fintype H] (f : ℕ) : Finset H :=
  Finset.univ.filter fun τ ↦ f ∣ orderOf τ

end TauCeti.NumberField.Chebotarev
end
