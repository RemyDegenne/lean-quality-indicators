public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

open Huber ValuationSpectrum

universe u

namespace PreAdicSpace

/-- An object of `𝒱^pre` is affinoid when it is isomorphic to the presentation-limit pre-adic
space of a Huber pair. The pair of definition is required to lie in the plus ring, as in the
construction of `presentationLimitPreAdicSpace`.

The existentially quantified type carries all of its topological-ring and Huber instances. This
keeps the property at the natural universe of `PreAdicSpace` and does not choose a global plus
ring or pair of definition. The definition is reducible so that the instances of
`ObjectProperty.isoClosure`, in particular closure under isomorphisms, apply to `isAffinoid`. -/
abbrev isAffinoid : ObjectProperty PreAdicSpace.{u} :=
  isAffinoidModel.isoClosure

end PreAdicSpace
end TauCeti
end
