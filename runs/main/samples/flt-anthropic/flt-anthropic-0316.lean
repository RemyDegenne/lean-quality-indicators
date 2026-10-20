namespace P2MW.S_HopfAlgebra_blockPieces_torsor_core_of_isAlgClosed

set_option autoImplicit false

set_option maxHeartbeats 1600000

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace S17

namespace TorsorCoreGen

open HopfAlgebra.TorsorGrading

open TensorProduct

variable (A : Type) [AddCommGroup A] [DecidableEq A]

variable {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H]

variable (π : H →ₐc[R] MonoidAlgebra R (Multiplicative A))

omit [DecidableEq A] in
theorem gradingCoaction_one :
    gradingCoaction A π (1 : H)
      = (1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] (1 : H) := by
  unfold gradingCoaction
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [Bialgebra.comul_one, Algebra.TensorProduct.one_def, LinearMap.rTensor_tmul]
  rw [show π.toLinearMap (1 : H) = 1 from map_one π]

end TorsorCoreGen
end S17
end
end P2MW.S_HopfAlgebra_blockPieces_torsor_core_of_isAlgClosed
