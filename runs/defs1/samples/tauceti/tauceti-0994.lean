public section

open CategoryTheory WithConv

namespace TauCeti

universe u

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A reduced finite-type affine group whose geometric points are all semisimple and unipotent is
the trivial group: its counit is a bialgebra equivalence with the base field. -/
noncomputable def counitBialgEquivOfGeometricallySemisimpleUnipotent
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H]
    (hsemisimple : geometricallySemisimplePointsCommHopfAlgProperty k H.obj)
    (hunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj) :
    H ≃ₐc[k] k :=
  BialgEquiv.ofBijective (Bialgebra.counitBialgHom k H)
    (counitBialgHom_bijective_of_geometricallySemisimple_of_geometricallyUnipotent
      H hsemisimple hunipotent)

end FiniteTypeCommHopfAlgCat
end TauCeti
end
