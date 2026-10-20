public section

open scoped TensorProduct ComplexOrder

namespace TauCeti.Hodge

open IsBaseChange

variable {V : Type*} {V' : Type*} {Vℂ : Type*} {V'ℂ : Type*}

variable [AddCommGroup V] [AddCommGroup V'] [AddCommGroup Vℂ] [Module ℂ Vℂ]

variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]

variable {ιℂ : V →ₗ[ℤ] Vℂ} {ι'ℂ : V' →ₗ[ℤ] V'ℂ}

variable {hℂ : IsBaseChange ℂ ιℂ} {h'ℂ : IsBaseChange ℂ ι'ℂ} {n n' : ℤ}

variable {hs : HodgeStructure hℂ n} {hs' : HodgeStructure h'ℂ n'}

@[simp]
theorem Polarization.tensorProduct_hodgeForm_tmul_tmul (P : Polarization hℂ hs)
    (P' : Polarization h'ℂ hs') (a c : Vℂ) (b d : V'ℂ) :
    (P.tensorProduct P').hodgeForm (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d) =
      P.hodgeForm a c * P'.hodgeForm b d := by
  rw [Polarization.hodgeForm_apply, Polarization.hodgeForm_apply,
    Polarization.hodgeForm_apply, Polarization.tensorProduct_Q,
    latticeConj_tensorLatticeMap_tmul hℂ h'ℂ, HodgeStructure.tensorProduct_weilOperator,
    TensorProduct.map_tmul, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]
  exact mul_comm _ _

end TauCeti.Hodge
end
