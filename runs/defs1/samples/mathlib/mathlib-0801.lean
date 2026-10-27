@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite IsLocalRing

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {U : X.Opens}

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obtain
a morphism of residue fields in the other direction. -/
def Hom.residueFieldMap (f : X ⟶ Y) (x : X) :
    Y.residueField (f x) ⟶ X.residueField x :=
  CommRingCat.ofHom <| IsLocalRing.ResidueField.map (f.stalkMap x).hom

end AlgebraicGeometry.Scheme
end
end
