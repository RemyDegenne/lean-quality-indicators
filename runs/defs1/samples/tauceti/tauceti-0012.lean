public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{v} (_root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})]

variable (S : J.MayerVietorisSquare) (F : _root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})

omit [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{v} (_root_.CategoryTheory.Sheaf J AddCommGrpCat.{v})] in
/-- The difference of the restrictions of sections from the two covering objects to
 their intersection. -/
def mayerVietorisSectionsDifference :
    (F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) →+ F.obj.obj (op S.X₁) :=
  ((F.obj.map S.f₁₂.op).hom.comp (AddMonoidHom.fst _ _)) -
    ((F.obj.map S.f₁₃.op).hom.comp (AddMonoidHom.snd _ _))

end TauCeti.CategoryTheory
end
end
