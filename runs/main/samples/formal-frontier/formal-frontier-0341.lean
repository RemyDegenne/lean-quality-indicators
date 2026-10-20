@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe uR uC uD uE uM uN uP uι uκ uI

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

section TensorMaps

variable {C : ModuleCat.{uC} R} {D : ModuleCat.{uD} R} {E : ModuleCat.{uE} R}

variable {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R} {P : TopModuleCat.{uP} R}

@[simp]
theorem tensorMapCLM_id :
    tensorMapCLM R (LinearMap.id : C →ₗ[R] C) (ContinuousLinearMap.id R M) =
      ContinuousLinearMap.id R (tensorLeftObj R C M) := by
  apply ContinuousLinearMap.coe_injective
  rw [tensorMapCLM_toLinearMap]
  change (TensorProduct.map (LinearMap.id : C →ₗ[R] C)
    (LinearMap.id : M →ₗ[R] M) :
    TensorProduct R C M →ₗ[R] TensorProduct R C M) = LinearMap.id
  exact TensorProduct.map_id

end TensorMaps
end TopModuleCat
end
