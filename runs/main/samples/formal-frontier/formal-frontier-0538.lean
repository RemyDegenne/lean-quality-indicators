@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace TopCat

@[reassoc]
theorem openMap_comp_inclusion {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U : Opens X) (W : Opens Y) (h : Set.MapsTo f U W) :
    openMap f U W h ≫ W.inclusion' = U.inclusion' ≫ f := rfl

end TopCat
end
end
