public section

open scoped TensorProduct TauCeti.GaloisDescent

namespace TauCeti.GaloisDescent

universe u_k u_L u_M

variable {k : Type u_k} {L : Type u_L} {M : Type u_M}

variable [Field k] [Field L] [Algebra k L]

variable [AddCommGroup M]

/-- The group-algebra antipode restricted to the Galois-invariant subalgebra. -/
noncomputable def groupAlgebraInvariantsAntipode
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho ≃ₐ[k] groupAlgebraInvariants rho := by
  exact AlgEquiv.ofAlgHom (groupAlgebraInvariantsAntipodeHom rho)
    (groupAlgebraInvariantsAntipodeHom rho)
    (AlgHom.ext fun x ↦ by
      rw [AlgHom.comp_apply, AlgHom.id_apply]
      apply Subtype.ext
      rw [coe_groupAlgebraInvariantsAntipodeHom_apply,
        coe_groupAlgebraInvariantsAntipodeHom_apply,
        HopfAlgebra.antipode_antipode])
    (AlgHom.ext fun x ↦ by
      rw [AlgHom.comp_apply, AlgHom.id_apply]
      apply Subtype.ext
      rw [coe_groupAlgebraInvariantsAntipodeHom_apply,
        coe_groupAlgebraInvariantsAntipodeHom_apply,
        HopfAlgebra.antipode_antipode])

end TauCeti.GaloisDescent
end
