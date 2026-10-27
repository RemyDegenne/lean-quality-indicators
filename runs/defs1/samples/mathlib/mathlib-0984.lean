@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

infixl:15 " ⊣ " => Adjunction

namespace Adjunction

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

variable {F : C ⥤ D} {G : D ⥤ C}

attribute [local simp] CoreHomEquivUnitCounit.homEquiv_unit CoreHomEquivUnitCounit.homEquiv_counit

section ConstructLeft

variable {F_obj : C → D}

variable (e : ∀ X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))

variable (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)

/-- Show that the functor given by `leftAdjointOfEquiv` is indeed left adjoint to `G`. Dual
to `adjunctionOfEquivRight`. -/
@[simps!]
def adjunctionOfEquivLeft : leftAdjointOfEquiv e he ⊣ G :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := fun {X'} {X} {Y} f g => by
        have {X : C} {Y Y' : D} (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
            (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
          rw [Equiv.symm_apply_eq, he]; simp
        simp [← this, ← he] }

end ConstructLeft
end Adjunction
end CategoryTheory
end
