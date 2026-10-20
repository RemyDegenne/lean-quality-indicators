@[expose] public section

open scoped TensorProduct

universe uR uC uD uC' uD'

namespace GroupLike

variable {R : Type uR} {C : Type uC} {D : Type uD}

variable [CommSemiring R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

local notation "πC" =>
  (CoalgHom.comp (CoalgEquiv.toCoalgHom (Coalgebra.TensorProduct.rid R R C))
    (Coalgebra.TensorProduct.map
      (CoalgHom.id R C) (Coalgebra.counitCoalgHom R D)))

local notation "πD" =>
  (CoalgHom.comp (CoalgEquiv.toCoalgHom (Coalgebra.TensorProduct.lid R D))
    (Coalgebra.TensorProduct.map
      (Coalgebra.counitCoalgHom R C) (CoalgHom.id R D)))

@[simp]
theorem tensorEquiv_symm_val (p : GroupLike R C × GroupLike R D) :
    ((tensorEquiv R C D).symm p).val = p.1.val ⊗ₜ[R] p.2.val := by
  change ((1 : R) • p.1.val) ⊗ₜ[R] ((1 : R) • p.2.val) = p.1.val ⊗ₜ[R] p.2.val
  simp only [one_smul]

end GroupLike
end
