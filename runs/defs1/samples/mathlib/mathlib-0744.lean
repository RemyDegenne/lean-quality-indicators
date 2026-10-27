@[expose] public section

universe v₁ v₂ v₃ u₁ u₂

noncomputable section

open CategoryTheory.Category

namespace CategoryTheory

attribute [instance 100] IsConnected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]

/-- Functions from connected components and functors to discrete category are in bijection -/
def ConnectedComponents.typeToCatHomEquiv (J) [Category* J] (X : Type*) :
    (ConnectedComponents J → X) ≃ (J ⥤ Discrete X) where
  toFun := ConnectedComponents.functorToDiscrete _
  invFun := ConnectedComponents.liftFunctor _
  left_inv f := funext fun x ↦ by
    obtain ⟨x, h⟩ := Quotient.exists_rep x
    rw [← h]
    rfl
  right_inv fctr :=
    Functor.hext (fun _ ↦ rfl) (fun c d f ↦
      have : Subsingleton (fctr.obj c ⟶ fctr.obj d) := Discrete.instSubsingletonDiscreteHom _ _
      (Subsingleton.elim (fctr.map f) _).symm.heq)

end CategoryTheory
end
end
