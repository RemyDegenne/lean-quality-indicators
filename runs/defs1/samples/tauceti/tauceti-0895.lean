public section

open CategoryTheory Topology

universe u

namespace TauCeti

namespace PretransitiveFundamentalGroupoidAction

variable {X : TopCat.{u}}

/-- The fully faithful inclusion into all fundamental-groupoid actions. -/
noncomputable abbrev forget (X : TopCat.{u}) :
    PretransitiveFundamentalGroupoidAction X ⥤ (FundamentalGroupoid X ⥤ Type u) :=
  ObjectProperty.ι _

end PretransitiveFundamentalGroupoidAction
end TauCeti
end
