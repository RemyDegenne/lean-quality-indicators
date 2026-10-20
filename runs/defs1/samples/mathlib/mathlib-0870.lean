@[expose] public section

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

attribute [instance] NonPreadditiveAbelian.has_zero_object

attribute [instance] NonPreadditiveAbelian.has_kernels

attribute [instance] NonPreadditiveAbelian.has_cokernels

attribute [instance] NonPreadditiveAbelian.has_finite_products

attribute [instance] NonPreadditiveAbelian.has_finite_coproducts

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [NonPreadditiveAbelian C]

namespace CategoryTheory.NonPreadditiveAbelian

section

attribute [local instance] hasSub

attribute [local instance] hasNeg

attribute [local instance] hasAdd

/-- Every `NonPreadditiveAbelian` category is preadditive. -/
@[instance_reducible]
def preadditive : Preadditive C where
  homGroup X Y :=
    { add_assoc := add_assoc
      zero_add := neg_neg
      add_zero := add_zero
      neg_add_cancel := neg_add_cancel
      sub_eq_add_neg f g := (add_neg f g).symm
      add_comm := add_comm
      nsmul := nsmulRec
      zsmul := zsmulRec }
  add_comp := add_comp
  comp_add := comp_add

end
end CategoryTheory.NonPreadditiveAbelian
end
end
