@[expose] public section

universe u v w w₁ uF

open scoped TensorProduct

namespace CoalgHomClass

section LinearMap

variable {R : Type u} {A : Type v} {B : Type w} {F : Type uF}

variable [CommSemiring R]

variable [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]

variable [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]

variable [FunLike F A B] [CoalgHomClass F R A B]

@[simp]
theorem toCoalgHom_toLinearMap (f : F) :
    (CoalgHomClass.toCoalgHom (F := F) (R := R) (A := A) (B := B) f).toLinearMap =
      (LinearMap.ofClass f : A →ₗ[R] B) := by
  apply LinearMap.ext
  intro x
  exact congrFun
    ((CoalgHom.coe_toLinearMap
      (CoalgHomClass.toCoalgHom (F := F) (R := R) (A := A) (B := B) f)).trans
      ((CoalgHom.coe_coe (R := R) f).trans
        (LinearMap.coe_ofClass (σ := RingHom.id R) (f := f)).symm)) x

end LinearMap
end CoalgHomClass
end
