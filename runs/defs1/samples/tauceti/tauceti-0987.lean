public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

open Huber ValuationSpectrum

universe u

/-- The full subcategory of affinoid pre-adic spaces. -/
abbrev AffinoidPreAdicSpace : Type (u + 1) :=
  PreAdicSpace.isAffinoid.{u}.FullSubcategory

end TauCeti
end
