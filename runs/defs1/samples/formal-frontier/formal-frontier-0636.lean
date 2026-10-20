@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite

universe v u w

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C]

variable {H G : Functor C GrpCat.{w}} (i : H ⟶ G)

/-- The natural transformation between group-valued functors whose components
send every element to the identity. -/
def trivialGrp : H ⟶ G where
  app _ := GrpCat.ofHom
    { toFun := fun _ ↦ 1
      map_one' := rfl
      map_mul' := by simp }
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    simp

end CategoryTheory.NatTrans
end
end
