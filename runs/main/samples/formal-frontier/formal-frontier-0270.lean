public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat.Sheaf.CommRingForget

universe v vj wj

namespace TopCat.Sheaf.CommRingForget

variable {W X Y : TopCat.{v}}

theorem canonicalComponent_triangleMap (q : W ⟶ Y) (f : Y ⟶ X)
    {A : X.Sheaf CommRingCat.{v}} {B : Y.Sheaf CommRingCat.{v}}
    (a : (TopCat.Sheaf.pullback CommRingCat.{v} f).obj A ⟶ B) :
    AlgebraicGeometry.SheafedSpace.triangleMap (Type v)
        (rfl : q ≫ f = q ≫ f)
        (canonicalComponent f A ≫ (underlyingSheaf Y).map a) ≫
      canonicalComponent q B =
    canonicalComponent (q ≫ f) A ≫
      (underlyingSheaf W).map
        (AlgebraicGeometry.SheafedSpace.triangleMap CommRingCat.{v}
          (rfl : q ≫ f = q ≫ f) a) := by
  change TopCat.Sheaf.pullbackCompInv (Type v) q f ((underlyingSheaf X).obj A) ≫
      (TopCat.Sheaf.pullback (Type v) q).map
        (canonicalComponent f A ≫ (underlyingSheaf Y).map a) ≫ canonicalComponent q B =
    canonicalComponent (q ≫ f) A ≫ (underlyingSheaf W).map
      (TopCat.Sheaf.pullbackCompInv CommRingCat.{v} q f A ≫
        (TopCat.Sheaf.pullback CommRingCat.{v} q).map a)
  simp only [Functor.map_comp, Category.assoc]
  rw [canonicalComponent_naturality]
  simpa only [Category.assoc] using congrArg
    (fun arrow ↦ arrow ≫ (underlyingSheaf W).map
      ((TopCat.Sheaf.pullback CommRingCat.{v} q).map a))
    (canonicalComponent_comp_inv q f A)

end TopCat.Sheaf.CommRingForget
end
end
