@[expose] public section

open CategoryTheory TopologicalSpace Topology

universe u

attribute [instance] TopCat.str

namespace TopCat

@[simp]
lemma ofHom_hom {X Y : TopCat.{u}} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

end TopCat
end
