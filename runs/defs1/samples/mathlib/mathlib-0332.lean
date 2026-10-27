@[expose] public section

universe w v' v u' u

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A]

variable [HasColimitsOfSize.{w, w} A]

/-- Given a point of a site, the skyscraper sheaf functor is right adjoint
to the fiber functor on sheaves. -/
noncomputable def skyscraperSheafAdjunction :
    Φ.sheafFiber (A := A) ⊣ Φ.skyscraperSheafFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        Φ.skyscraperPresheafHomEquiv.trans
          ((fullyFaithfulSheafToPresheaf J A).homEquiv (Y := Φ.skyscraperSheaf M)).symm
      homEquiv_naturality_left_symm f g :=
        Φ.skyscraperPresheafHomEquiv_naturality_left_symm f.hom g.hom
      homEquiv_naturality_right f g := by
        ext : 1
        exact Φ.skyscraperPresheafHomEquiv_naturality_right f g }

end CategoryTheory.GrothendieckTopology.Point
end
