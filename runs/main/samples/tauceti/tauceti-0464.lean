public section

open scoped TensorProduct

universe u v

variable {R ι : Type u} {M : Type v}

namespace SymmetricPower

section Symmetrization

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]

@[simp]
theorem toTensorPower_tprod (m : ι → M) :
    toTensorPower R ι M (⨂ₛ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [tprod, LinearMap.compMultilinearMap_apply, toTensorPower_mk']
  exact symmetrizer_tprod m

end Symmetrization
end SymmetricPower
end
