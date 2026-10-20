public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- The **degree-zero relative Picard fppf sheaf** of a smooth proper geometrically connected
family of curves, obtained by sheafifying the presheaf of classes having degree zero on every
geometric fibre. -/
def relativePicardDegreeZeroFppfSheaf :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (relativePicardDegreeZeroAddPresheaf f)

end
end TauCeti.AlgebraicGeometry
end
