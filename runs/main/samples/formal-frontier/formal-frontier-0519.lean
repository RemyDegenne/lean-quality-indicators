public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat.Sheaf.AbelianForget

universe v vj wj

namespace TopCat.Sheaf.AbelianForget

variable {W X Y : TopCat.{v}}

theorem canonicalComponent_triangleMap (q : W ⟶ Y) (f : Y ⟶ X)
    {A : X.Sheaf AddCommGrpCat.{v}} {B : Y.Sheaf AddCommGrpCat.{v}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} f).obj A ⟶ B) :
    AlgebraicGeometry.SheafedSpace.triangleMap (Type v)
        (rfl : q ≫ f = q ≫ f)
        (canonicalComponent f A ≫ (underlyingSheaf Y).map a) ≫
      canonicalComponent q B =
    canonicalComponent (q ≫ f) A ≫
      (underlyingSheaf W).map
        (AlgebraicGeometry.SheafedSpace.triangleMap AddCommGrpCat.{v}
          (rfl : q ≫ f = q ≫ f) a) := by
  change TopCat.Sheaf.pullbackCompInv (Type v) q f ((underlyingSheaf X).obj A) ≫
      (TopCat.Sheaf.pullback (Type v) q).map
        (canonicalComponent f A ≫ (underlyingSheaf Y).map a) ≫ canonicalComponent q B =
    canonicalComponent (q ≫ f) A ≫ (underlyingSheaf W).map
      (TopCat.Sheaf.pullbackCompInv AddCommGrpCat.{v} q f A ≫
        (TopCat.Sheaf.pullback AddCommGrpCat.{v} q).map a)
  simp only [Functor.map_comp, Category.assoc]
  rw [canonicalComponent_naturality]
  simpa only [Category.assoc] using congrArg
    (fun arrow ↦ arrow ≫ (underlyingSheaf W).map
      ((TopCat.Sheaf.pullback AddCommGrpCat.{v} q).map a))
    (canonicalComponent_comp_inv q f A)

end TopCat.Sheaf.AbelianForget
end
end
