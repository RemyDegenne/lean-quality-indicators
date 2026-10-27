@[expose] public section

noncomputable section

namespace CategoryTheory

universe v u v₁ u₁ v₂ u₂

variable (C : Type u) [Category.{v} C]

namespace FreeGroupoid

variable {C}

section UniversalProperty

variable {G : Type u₁} [Groupoid.{v₁} G]

set_option backward.isDefEq.respectTransparency false in
/-- The lift of a functor from `C` to a groupoid to a functor from
`FreeGroupoid C` to the groupoid -/
def lift (φ : C ⥤ G) : FreeGroupoid C ⥤ G :=
  Quotient.lift (FreeGroupoid.homRel C) (Quiver.FreeGroupoid.lift φ.toPrefunctor)
    (fun _ _ f g r ↦ by
      have {X Y : C} (f : X ⟶ Y) :=
        Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec φ.toPrefunctor) f
      induction r <;> cat_disch)

end UniversalProperty
end FreeGroupoid
end CategoryTheory
end
end
