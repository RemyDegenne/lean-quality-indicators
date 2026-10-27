public section

open scoped TensorProduct

namespace TauCeti

universe u uR uA uM

attribute [local instance] Comodule.cofree

section Cochains

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

open TensorWords

namespace AInfinityRightModule

variable {AA : AInfinityAlgebra R A} {M : Type uM} [AddCommGroup M] [Module R M]
  (MM : AInfinityRightModule AA M) {e : A}

/-- The Yoneda cochain of `x`: the cochain out of the free module of rank one whose Taylor map
sends `y ⊗ w` to the module Taylor map of `x ⊗ y w`, after the degree-one Koszul twist of `x`.
On unsuspended operations it is `(a₁, …, aₙ) ↦ m_{n+1}(x, a₁, …, aₙ)` up to the suspension
signs. -/
noncomputable def yonedaCochain :
    M →ₗ[R] A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A where
  toFun x := (Comodule.Hom.cofreeLift (C := TensorWords R A)
    (MM.taylor ∘ₗ tmulConcat R A M (MM.grading.koszulTwist 1 x))).toLinearMap
  map_add' _ _ := by
    simp only [map_add, LinearMap.comp_add, Comodule.Hom.cofreeLift_toLinearMap,
      LinearMap.rTensor_add, LinearMap.add_comp]
  map_smul' _ _ := by
    simp only [map_smul, LinearMap.comp_smul, Comodule.Hom.cofreeLift_toLinearMap,
      LinearMap.rTensor_smul, LinearMap.smul_comp, RingHom.id_apply]

end AInfinityRightModule
end Cochains
end TauCeti
end
