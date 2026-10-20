@[expose] public section

open scoped MonoidAlgebra

variable (R X : Type*) [CommSemiring R]

namespace FreeAlgebra

attribute [local instance] Pre.hasCoeGenerator Pre.hasCoeSemiring Pre.hasMul Pre.hasAdd
  Pre.hasZero Pre.hasOne Pre.hasSMul

variable {X}

variable {A : Type*} [Semiring A] [Algebra R A]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given a function `f : X → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `FreeAlgebra R X → A`. -/
@[irreducible]
def lift : (X → A) ≃ (FreeAlgebra R X →ₐ[R] A) :=
  { toFun := liftAux R
    invFun := fun F ↦ F ∘ ι R
    left_inv := fun f ↦ by
      ext
      simp only [Function.comp_apply, ι_def]
      rfl
    right_inv := fun F ↦ by
      ext t
      rcases t with ⟨x⟩
      induction x with
      | of =>
        change ((F : FreeAlgebra R X → A) ∘ ι R) _ = _
        simp only [Function.comp_apply, ι_def]
      | ofScalar x =>
        change algebraMap _ _ x = F (algebraMap _ _ x)
        rw [AlgHom.commutes F _]
      | add a b ha hb =>
        -- Porting note: it is necessary to declare fa and fb explicitly otherwise Lean refuses
        -- to consider `Quot.mk (Rel R X) ·` as element of FreeAlgebra R X
        let fa : FreeAlgebra R X := Quot.mk (Rel R X) a
        let fb : FreeAlgebra R X := Quot.mk (Rel R X) b
        change liftAux R (F ∘ ι R) (fa + fb) = F (fa + fb)
        grind
      | mul a b ha hb =>
        let fa : FreeAlgebra R X := Quot.mk (Rel R X) a
        let fb : FreeAlgebra R X := Quot.mk (Rel R X) b
        change liftAux R (F ∘ ι R) (fa * fb) = F (fa * fb)
        grind }

end FreeAlgebra
end
