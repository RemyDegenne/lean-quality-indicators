public section

set_option warningAsError true

open CategoryTheory TopologicalSpace

open CategoryTheory.Functor CategoryTheory.Adjunction CategoryTheory.NatTrans
  CategoryTheory.TwoSquare

noncomputable section

universe v

namespace TopCat.Sheaf.OpenBaseChange

/-- The canonical map from the inverse-image open subspace `f⁻¹(V)` to `V`. -/
@[expose] def preimageMap {X Y : TopCat.{v}} (f : X ⟶ Y) (V : Opens Y) :
    (Opens.toTopCat X).obj ((Opens.map f).obj V) ⟶ (Opens.toTopCat Y).obj V :=
  TopCat.ofHom
    { toFun := fun x ↦ ⟨f x.1, x.2⟩
      continuous_toFun :=
        (f.hom.continuous.comp continuous_subtype_val).subtype_mk _ }

end TopCat.Sheaf.OpenBaseChange
end
end
