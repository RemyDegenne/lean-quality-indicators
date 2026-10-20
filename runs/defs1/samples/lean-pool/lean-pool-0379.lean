@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits Opposite

universe v u v' u'

variable {A : Type u}

section TensorCoend

section

/-- Descend a right-whiskered dinatural family through a tensor by
a coend. -/
noncomputable def tensorRightCoendDesc
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {J : Type u}
    [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ D) [HasCoend F] (W : D)
    [PreservesColimit (multispanIndexCoend F).multispan (tensorRight W)]
    {Z : D} (k : ∀ j : J, (F.obj (op j)).obj j ⊗ W ⟶ Z)
    (hk : ∀ ⦃i j : J⦄ (g : i ⟶ j), ((F.map g.op).app i ▷ W) ≫ k i = ((F.obj
      (op j)).map g ▷ W) ≫ k j) : coend F ⊗ W ⟶ Z :=
  (isColimitOfPreserves (tensorRight W)
    (colimit.isColimit (multispanIndexCoend F).multispan)).desc
      (tensorRightCoendCocone F W k hk)

end
end TensorCoend
end RS
end
