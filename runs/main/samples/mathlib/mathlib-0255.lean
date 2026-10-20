@[expose] public section

open CategoryTheory

universe v u

attribute [instance] PartOrd.str

namespace PartOrd

@[simp]
lemma hom_ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X →o Y) : (ofHom f).hom = f :=
  rfl

end PartOrd
end
