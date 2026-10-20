@[expose] public section

noncomputable section

namespace CategoryTheory.Limits

open CategoryTheory

universe w w' v u u₂

variable {J : Type w}

open WalkingParallelFamily

open WalkingParallelFamily.Hom

attribute [local aesop safe cases] WalkingParallelFamily.Hom

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (f : J → (X ⟶ Y))

variable {f}

/-- To construct an isomorphism between cotridents,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
def Cotrident.ext [Nonempty J] {s t : Cotrident f} (i : s.pt ≅ t.pt)
    (w : s.π ≫ i.hom = t.π := by cat_disch) : s ≅ t where
  hom := Cotrident.mkHom i.hom w
  inv := Cotrident.mkHom i.inv (by rw [Iso.comp_inv_eq, w])

end CategoryTheory.Limits
end
end
