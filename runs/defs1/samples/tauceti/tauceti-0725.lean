public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace TauCeti.TopCat

variable {X : TopCat.{v}} {ι : Type u} (U : ι → Opens X)

/-- The open set represented by a Čech index: the intersection of its family members. -/
def cechIntersection (s : CechIndex ι) : Opens X :=
  s.1.inf U

end TauCeti.TopCat
end
end
