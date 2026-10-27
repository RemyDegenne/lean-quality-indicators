public section

open CategoryTheory TopologicalSpace

namespace TauCeti

universe u

/-- Wedhorn's category `(PreAd)` of pre-adic spaces: the full subcategory of `𝒱^pre` whose objects
are the locally affinoid objects with structure presheaf adapted to their open affinoid subspaces
(`PreAdicSpace.isPreAdic`). -/
abbrev WedhornPreAdicSpace : Type (u + 1) :=
  PreAdicSpace.isPreAdic.{u}.FullSubcategory

end TauCeti
end
