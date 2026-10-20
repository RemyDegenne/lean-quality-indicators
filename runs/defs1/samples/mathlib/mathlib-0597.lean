@[expose] public section

open Function LinearMap Matrix Module TensorProduct

variable {ι R M N P Q : Type*}

attribute [local ext high] TensorProduct.ext

section Contraction

section CommSemiring

variable [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]

variable [Module R M] [Module R N] [Module R P] [Module R Q]

section Fintype

variable [DecidableEq ι] [Fintype ι] (b : Basis ι R M)

attribute [-ext] AlgebraTensorModule.curry_injective in
/-- If `M` is free, the natural linear map $M^* ⊗ N → Hom(M, N)$ is an equivalence. This function
provides this equivalence in return for a basis of `M`. -/
-- We manually create simp-lemmas because `@[simps]` generates a malformed lemma
noncomputable def dualTensorHomEquivOfBasis : Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  LinearEquiv.ofLinearMap (dualTensorHom R M N)
    (∑ i, TensorProduct.mk R _ N (b.dualBasis i) ∘ₗ (LinearMap.applyₗ (R := R) (b i)))
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, Basis.coord_apply, ←
        f.map_smul, _root_.map_sum (dualTensorHom R M N), ← _root_.map_sum f, b.sum_repr])
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, compr₂ₛₗ_apply,
        tmul_smul, smul_tmul', ← sum_tmul, Basis.sum_dual_apply_smul_coord])

end Fintype
end CommSemiring
end Contraction
end
