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

variable (R C D) in
/-- Normalized group-like elements of a tensor product correspond to ordered pairs of
normalized group-like elements. The projections apply the opposite counit and a tensor
unitor; the inverse tensors the scalar-source point morphisms. -/
noncomputable def tensorEquiv :
    GroupLike R (C ⊗[R] D) ≃ GroupLike R C × GroupLike R D where
  toFun x := (GroupLike.map πC x, GroupLike.map πD x)
  invFun p :=
    (GroupLike.coalgHomEquiv (R := R) (C := C ⊗[R] D)).symm
      ((Coalgebra.TensorProduct.map
          (GroupLike.coalgHomEquiv (R := R) (C := C) p.1)
          (GroupLike.coalgHomEquiv (R := R) (C := D) p.2)).comp
        (Coalgebra.TensorProduct.lid R R).symm.toCoalgHom)
  left_inv x := by
    apply GroupLike.ext
    change ((1 : R) • πC x.val) ⊗ₜ[R] ((1 : R) • πD x.val) = x.val
    simp only [one_smul]
    have h := LinearMap.congr_fun
      (counit_tensor_contraction (R := R) (C := C) (D := D)) x.val
    simpa only [CoalgHom.toLinearMap_eq_coe, CoalgHom.coe_toLinearMap,
      LinearMap.comp_apply, LinearMap.id_apply,
      x.isGroupLikeElem_val.comul_eq_tmul_self, TensorProduct.map_tmul] using h
  right_inv p := by
    apply Prod.ext
    · apply GroupLike.ext
      change πC (((1 : R) • p.1.val) ⊗ₜ[R] ((1 : R) • p.2.val)) = p.1.val
      simp only [one_smul]
      change Coalgebra.counit (R := R) p.2.val • p.1.val = p.1.val
      rw [p.2.isGroupLikeElem_val.counit_eq_one, one_smul]
    · apply GroupLike.ext
      change πD (((1 : R) • p.1.val) ⊗ₜ[R] ((1 : R) • p.2.val)) = p.2.val
      simp only [one_smul]
      change Coalgebra.counit (R := R) p.1.val • p.2.val = p.2.val
      rw [p.1.isGroupLikeElem_val.counit_eq_one, one_smul]

end GroupLike
end
