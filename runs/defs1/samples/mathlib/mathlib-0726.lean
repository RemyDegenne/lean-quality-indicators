@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe v u w

noncomputable section

namespace CategoryTheory

namespace Mon

variable {J : Type w} [Category* J]

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

open MonObj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.hasLimitsOfShape`:
the proposed cone over a functor `F : J ⥤ Mon C` is a limit cone.
-/
@[simps]
def limitConeIsLimit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    IsLimit (limitCone F c hc) where
  lift s :=
    { hom := hc.lift ((Mon.forget C).mapCone s)
      isMonHom_hom.mul_hom := hc.hom_ext <| by simp
      isMonHom_hom.one_hom := hc.hom_ext <| by simp }
  fac s h := by ext; simp
  uniq s m w := Hom.ext' <| hc.hom_ext fun j ↦ by simpa using congr($(w j).hom)

end Mon
end CategoryTheory
end
end
