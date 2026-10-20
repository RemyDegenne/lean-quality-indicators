public section

open scoped TensorProduct

open TauCeti.GaloisDescent

namespace Representation.IntertwiningMap

variable {k L M N P : Type*}

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

variable [Field k] [Field L] [Algebra k L]

variable {rho : Representation ℤ (L ≃ₐ[k] L) M}

variable {tau : Representation ℤ (L ≃ₐ[k] L) N}

variable {upsilon : Representation ℤ (L ≃ₐ[k] L) P}

variable [FiniteDimensional k L] [IsGalois k L]

@[simp]
theorem groupAlgebraInvariantsBialgHom_id :
    groupAlgebraInvariantsBialgHom (Representation.IntertwiningMap.id rho) =
      BialgHom.id k (groupAlgebraInvariants rho) := by
  apply BialgHom.coe_toAlgHom_injective
  simp

end Representation.IntertwiningMap
end
