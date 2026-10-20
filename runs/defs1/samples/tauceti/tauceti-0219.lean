public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The inclusion of a candidate subgroup into the unipotent radical. -/
noncomputable def unipotentRadicalSpecMapOfCandidate
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H)
    (hI : HopfIdeal.IsUnipotentRadicalCandidate H I) :
    CommHopfAlgCat.quotientSpec H.obj I ⟶ unipotentRadicalSpec H :=
  CommHopfAlgCat.quotientSpecMapOfLe H.obj (unipotentRadicalDefiningIdeal_le H I hI)

end FiniteTypeCommHopfAlgCat
end
end TauCeti
end
