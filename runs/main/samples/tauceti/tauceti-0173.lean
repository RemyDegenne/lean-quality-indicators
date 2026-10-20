public section

open CategoryTheory AlgebraicGeometry Opposite WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

@[simp]
theorem range_identityComponentPointsHom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k) :
    (identityComponentPointsHom H A).hom.range =
      CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) A := by
  rfl

end TauCeti.FiniteTypeCommHopfAlgCat
end
