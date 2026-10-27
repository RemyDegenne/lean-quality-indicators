public section

set_option warningAsError true

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace

namespace TopCat.Sheaf.AbelianForget

variable {X Y : TopCat.{v}} (g : X ⟶ Y)

/-- The comparison from pullback of the underlying sheaf to the underlying
additive pullback, defined as the native Type-valued adjunction mate of the
forgotten additive unit. -/
noncomputable def canonicalComponent (A : Y.Sheaf AddCommGrpCat.{v}) :
    (TopCat.Sheaf.pullback (Type v) g).obj ((underlyingSheaf Y).obj A) ⟶
      (underlyingSheaf X).obj ((TopCat.Sheaf.pullback AddCommGrpCat.{v} g).obj A) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _).symm
    ((underlyingSheaf Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).unit.app A))

end TopCat.Sheaf.AbelianForget
end
