set_option warningAsError true

@[expose] public section

namespace TensorPower

open scoped TensorProduct

variable {K ι M N : Type*} [Field K] [Fintype ι]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- Tensor the scalar sum in each slot, then tensor its result with the identity on `N`. -/
noncomputable def scalarSumTensor (s : ℕ) (a : ι → K) :
    (TensorPower K s (ι → M)) ⊗[K] N →ₗ[K] (TensorPower K s M) ⊗[K] N :=
  (PiTensorProduct.map (fun _ : Fin s => scalarSum (M := M) a)).rTensor N

end TensorPower
end
