@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J K : Type*} [Category* J] [Category* K]

variable {C : Type*} [Category* C]

variable (F : J ⥤ K ⥤ C) (G : J × K ⥤ C)

variable {F}

set_option backward.defeqAttrib.useBackward true in
/-- Given a diagram `D` of colimit cocones under the `curry.obj G j`, and a cocone under `G`,
we can construct a cocone under the diagram consisting of the cocone points from `D`.
-/
@[simps]
def coconeOfCoconeCurry {D : DiagramOfCocones (curry.obj G)} (Q : ∀ j, IsColimit (D.obj j))
    (c : Cocone G) : Cocone D.coconePoints where
  pt := c.pt
  ι :=
    { app j := (Q j).desc
        { pt := c.pt
          ι := { app k := c.ι.app (j, k) } }
      naturality {j _} _ := (Q j).hom_ext (by simp) }

end CategoryTheory.Limits
end
