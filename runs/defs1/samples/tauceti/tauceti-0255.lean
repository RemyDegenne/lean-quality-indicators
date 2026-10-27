public section

open scoped TensorProduct

universe u v

namespace TauCeti.CommHopfAlgCat

open CategoryTheory

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R} {A : Subalgebra R H}

variable [Module.Flat R H] [Module.Flat R A]

/-- The inclusion of a Hopf subalgebra as a morphism of commutative Hopf algebras. -/
@[expose] noncomputable def hopfSubalgebraι (hA : A.IsHopfSubalgebra) :
    ofHopfSubalgebra hA ⟶ H :=
  _root_.CommHopfAlgCat.ofHom hA.valBialgHom

end TauCeti.CommHopfAlgCat
end
