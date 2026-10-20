@[expose] public section

noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (f : X ⟶ Y)

attribute [instance] MonoFactorisation.m_mono

variable {f}

variable (f)

namespace ImageFactorisation

/--
Copying an image factorisation to another image factorisation with propositionally equal
`m` and `e` fields.
-/
@[simps]
def copy {f : X ⟶ Y} (F : ImageFactorisation f) (m : F.F.I ⟶ Y) (e : X ⟶ F.F.I)
    (hm : m = F.F.m := by cat_disch) (he : e = F.F.e := by cat_disch) :
    ImageFactorisation f where
  F := F.F.copy m e
  isImage := F.isImage.copy m e

end ImageFactorisation
end CategoryTheory.Limits
end
end
