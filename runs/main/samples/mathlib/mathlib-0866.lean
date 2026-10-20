@[expose] public section

universe u v

open CategoryTheory

attribute [instance] BddOrd.isBoundedOrder

namespace BddOrd

lemma inv_hom_apply {X Y : BddOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

end BddOrd
end
