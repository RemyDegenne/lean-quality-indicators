public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

theorem geometricallyConnected_of_reductiveAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : reductiveAffineGroupSchemeProperty k G) :
    GeometricallyConnected G.obj.obj.X.hom := by
  exact (geometricallyConnected_iff_geometricallyConnected_coordinate k G).mpr
    ((reductiveAffineGroupSchemeProperty_iff k G).mp hG).geometricallyConnected

end TauCeti
end
