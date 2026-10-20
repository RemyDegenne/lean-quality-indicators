public section

open CategoryTheory

open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u

@[simp]
lemma geometricallyConnectedAffineGroupSchemeProperty_iff (S : CommRingCat.{u})
    (G : AffineGroupSchemeCat S) :
    geometricallyConnectedAffineGroupSchemeProperty S G ↔
      GeometricallyConnected G.obj.X.hom :=
  Iff.rfl

end TauCeti
end
