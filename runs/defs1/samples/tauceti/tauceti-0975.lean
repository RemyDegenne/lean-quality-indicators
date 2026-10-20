public section

namespace TauCeti.E6Minuscule

open CategoryTheory

open TauCeti.UniversalEnvelopingAlgebra

universe v w

variable (A : Type v) [CommRing A]

section BaseChange

variable (k : Type v) (K : Type max v w) [CommRing k] [CommRing K] [Algebra k K]

/-- The coordinate Hopf algebras of the generators over `K` are the scalar extensions of those
over `k`. -/
noncomputable def generatorCoordinateAlgebraBaseChangeIso :
    ∀ j, CommHopfAlgCat.baseChange (K := K) (generatorCoordinateAlgebra k j) ≅
      generatorCoordinateAlgebra K j
  | .inl _ => AdditiveGroup.coordinateHopfAlgebraBaseChangeIso k K
  | .inr _ => _root_.CommHopfAlgCat.isoMk
      (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k K
        (G := SplitTorus.characterGroup (Fin 6)))

end BaseChange
end TauCeti.E6Minuscule
end
