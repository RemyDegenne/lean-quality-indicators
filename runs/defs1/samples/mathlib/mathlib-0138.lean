@[expose] public section

universe v' u' v u

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {J : Type u'} [Category.{v'} J]

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D] {K : C ⥤ D}

variable {X : C}

namespace CategoryTheory.CostructuredArrow

namespace CreatesConnected

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) Given a cone in the base category, raise it to a cone in
`CostructuredArrow K B`. Note this is where the connected assumption is used.
-/
@[simps]
def raiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
    (c : Cone (F ⋙ CostructuredArrow.proj K B)) :
    Cone F where
  pt := CostructuredArrow.mk
    (K.map (c.π.app (Classical.arbitrary J)) ≫ (F.obj (Classical.arbitrary J)).hom)
  π.app j := CostructuredArrow.homMk (c.π.app j) <| by
    let z : (Functor.const J).obj (K.obj c.pt) ⟶ _ :=
      (CategoryTheory.Functor.constComp J c.pt K).inv ≫ Functor.whiskerRight c.π K ≫
        natTransInCostructuredArrow F
    convert! (nat_trans_from_is_connected z j (Classical.arbitrary J)) <;> simp [z]
  π.naturality X Y f := by
    apply CommaMorphism.ext
    · simpa using (c.w f).symm
    · simp

end CreatesConnected
end CategoryTheory.CostructuredArrow
end
end
