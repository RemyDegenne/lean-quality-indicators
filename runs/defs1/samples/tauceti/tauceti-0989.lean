public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {S : Type u} [CommRing S] {v w : S}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

variable {X X' X'' : MatrixFactorization S v} {Y Y' Y'' : MatrixFactorization S w}

/-- The tensor product of closed maps of matrix factorizations: the tensor product of the
underlying maps of curved duplexes. -/
noncomputable def tensorHom (f : X ⟶ X') (g : Y ⟶ Y') : tensorObj X Y ⟶ tensorObj X' Y' :=
  ⟨CurvedDuplex.tensorHom f.hom g.hom⟩

end TauCeti.MatrixFactorization
end
