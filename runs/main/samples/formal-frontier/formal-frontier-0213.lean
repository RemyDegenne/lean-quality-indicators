@[expose] public section

universe uR uS uT uι uκ uν

open Function

open scoped Matrix

namespace Module

section TensorCompatibility

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]

open Classical in
theorem rightFreeLinearMapScalarExtension_eq_rightExtension
    (f : R →+* S) (g : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R)) :
    rightFreeLinearMapScalarExtension R ι κ f g =
      LinearEquiv.arrowCongrAddEquiv
        (ModuleCat.RightExtension.rightFreeLinearEquiv f ι)
        (ModuleCat.RightExtension.rightFreeLinearEquiv f κ)
        (ModuleCat.RightExtension.map f g) := by
  have h :
      (rightFreeLinearMapScalarExtension R ι κ f g).comp
          (ModuleCat.RightExtension.rightFreeLinearEquiv f ι).toLinearMap =
        (ModuleCat.RightExtension.rightFreeLinearEquiv f κ).toLinearMap.comp
          (ModuleCat.RightExtension.map f g) := by
    apply ModuleCat.RightExtension.linearMap_ext f
    intro x s
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      ModuleCat.RightExtension.map_tmul, ModuleCat.RightExtension.rightFreeLinearEquiv_tmul]
    have hsmul : (fun j ↦ f (x j) * s) =
        MulOpposite.op s • (fun j ↦ f (x j)) := rfl
    rw [hsmul, map_smul, rightFreeLinearMapScalarExtension_coefficients]
    rfl
  apply LinearMap.ext
  intro y
  change rightFreeLinearMapScalarExtension R ι κ f g y =
    ModuleCat.RightExtension.rightFreeLinearEquiv f κ
      (ModuleCat.RightExtension.map f g
        ((ModuleCat.RightExtension.rightFreeLinearEquiv f ι).symm y))
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] using
    DFunLike.congr_fun h ((ModuleCat.RightExtension.rightFreeLinearEquiv f ι).symm y)

end TensorCompatibility
end Module
end
