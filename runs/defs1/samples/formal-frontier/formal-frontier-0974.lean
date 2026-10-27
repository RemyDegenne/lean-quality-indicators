public section

set_option warningAsError true

universe v

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf.CommRingForget

/-- Forget ring structure in a sheaf of commutative rings on `Z`. -/
@[expose] noncomputable def underlyingSheaf (Z : TopCat.{v}) :
    Z.Sheaf CommRingCat.{v} ⥤ Z.Sheaf (Type v) :=
  sheafCompose (Opens.grothendieckTopology Z) (CategoryTheory.forget CommRingCat.{v})

end TopCat.Sheaf.CommRingForget
end
