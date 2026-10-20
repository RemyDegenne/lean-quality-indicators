public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The canonical inclusion of the unipotent radical into the ambient affine group scheme. -/
noncomputable abbrev unipotentRadicalSpecι (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalSpec H ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).obj (op H.obj) :=
  CommHopfAlgCat.quotientSpecι H.obj (unipotentRadicalDefiningIdeal H)

end FiniteTypeCommHopfAlgCat
end
end TauCeti
end
