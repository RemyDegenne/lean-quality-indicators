@[expose] public section

open scoped TensorProduct

universe uR uC uM uN uD uM' uN'

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- Tensoring an algebraic product of coefficients with a topological right
module distributes over the product. The underlying equivalence is
`TensorProduct.prodLeft R R C D M`; no topology on the coefficients is used. -/
noncomputable def tensorProdLeft (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R)
    (M : TopModuleCat.{uM} R) :
    tensorLeftObj R (ModuleCat.of R (C × D)) M ≃L[R]
      (tensorLeftObj R C M × tensorLeftObj R D M) where
  toLinearEquiv := TensorProduct.prodLeft R R C D M
  continuous_toFun := by
    let f := (tensorMapCLM R (C := ModuleCat.of R (C × D)) (D := C)
      (M := M) (N := M) (LinearMap.fst R C D) (ContinuousLinearMap.id R M)).prod
      (tensorMapCLM R (C := ModuleCat.of R (C × D)) (D := D)
        (M := M) (N := M) (LinearMap.snd R C D) (ContinuousLinearMap.id R M))
    have heq : (TensorProduct.prodLeft R R C D M).toLinearMap = f.toLinearMap := by
      apply TensorProduct.ext'
      rintro ⟨c, d⟩ m
      exact TensorProduct.prodLeft_tmul R R C D M c d m
    exact f.continuous.congr (fun z ↦ (DFunLike.congr_fun heq z).symm)
  continuous_invFun := by
    let e : tensorLeftObj R (ModuleCat.of R (C × D)) M ≃ₗ[R]
        (tensorLeftObj R C M × tensorLeftObj R D M) :=
      TensorProduct.prodLeft R R C D M
    let l := tensorMapCLM R (C := C) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M)
    let r := tensorMapCLM R (C := D) (D := ModuleCat.of R (C × D))
      (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M)
    let i := l.coprod r
    have h : e.toLinearMap.comp i.toLinearMap =
        LinearMap.id (R := R) (M := tensorLeftObj R C M × tensorLeftObj R D M) := by
      apply LinearMap.prod_ext
      · apply TensorProduct.ext'
        intro c m
        have hi : i (c ⊗ₜ[R] m, 0) =
            (((c, 0) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
          (DFunLike.congr_fun (ContinuousLinearMap.coprod_comp_inl l r)
            (c ⊗ₜ[R] m)).trans
              (tensorMapCLM_tmul R (C := C) (D := ModuleCat.of R (C × D))
                (M := M) (N := M) (LinearMap.inl R C D) (ContinuousLinearMap.id R M) c m)
        exact (congrArg e hi).trans
          ((TensorProduct.prodLeft_tmul R R C D M c 0 m).trans
            (congrArg (fun z : tensorLeftObj R D M ↦ (c ⊗ₜ[R] m, z))
              (TensorProduct.zero_tmul (R := R) D m)))
      · apply TensorProduct.ext'
        intro d m
        have hi : i (0, d ⊗ₜ[R] m) =
            (((0, d) : ModuleCat.of R (C × D)) ⊗ₜ[R] m) :=
          (DFunLike.congr_fun (ContinuousLinearMap.coprod_comp_inr l r)
            (d ⊗ₜ[R] m)).trans
              (tensorMapCLM_tmul R (C := D) (D := ModuleCat.of R (C × D))
                (M := M) (N := M) (LinearMap.inr R C D) (ContinuousLinearMap.id R M) d m)
        exact (congrArg e hi).trans
          ((TensorProduct.prodLeft_tmul R R C D M 0 d m).trans
            (congrArg (fun z : tensorLeftObj R C M ↦ (z, d ⊗ₜ[R] m))
              (TensorProduct.zero_tmul (R := R) C m)))
    have heq : e.symm.toLinearMap = i.toLinearMap := by
      apply LinearMap.ext
      intro p
      apply e.injective
      exact (e.apply_symm_apply p).trans (DFunLike.congr_fun h p).symm
    exact i.continuous.congr (fun p ↦ (DFunLike.congr_fun heq p).symm)

end TopModuleCat
end
