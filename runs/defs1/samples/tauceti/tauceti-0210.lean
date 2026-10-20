public section

namespace TauCeti

universe u v w

attribute [instance] WedderburnPresentation.instDivisionRing WedderburnPresentation.instNeZeroDegree

attribute [instance] WedderburnAlgebraPresentation.instDivisionRing
  WedderburnAlgebraPresentation.instAlgebra WedderburnAlgebraPresentation.instNeZeroDegree

attribute [instance] FiniteWedderburnAlgebraPresentation.instModuleFinite

attribute [instance] SplitWedderburnAlgebraPresentation.instNeZeroDegree

attribute [instance] WedderburnEndomorphismAlgebraPresentation.instIsSimpleModule
  WedderburnEndomorphismAlgebraPresentation.instNeZeroDegree

namespace SplitWedderburnAlgebraPresentation

variable {K : Type v} {A : Type u} [Field K] [Ring A] [Algebra K A]

/-- View a split Wedderburn presentation as a general algebraic Wedderburn presentation whose
division rings are all `K`. -/
@[expose]
def toWedderburnAlgebraPresentation (P : SplitWedderburnAlgebraPresentation K A) :
    WedderburnAlgebraPresentation.{u, v, v} K A where
  blockCount := P.blockCount
  divisionRing := fun _ ↦ K
  degree := P.degree
  equiv := P.equiv

end SplitWedderburnAlgebraPresentation
end TauCeti
end
