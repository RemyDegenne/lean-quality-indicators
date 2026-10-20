@[expose] public section

universe uR uS uM uN

open CategoryTheory

open scoped TensorProduct

namespace ModuleCat.RightExtension

section RingTarget

variable {R : Type uR} {S : Type uS} [CommRing R] [Ring S]

variable (φ : R →+* S)

/-- Tensor extension of a source morphism, linear for the right action on the
coefficient factor. Its underlying function is Mathlib's tensor map, with the
identity on the coefficient module restricted along `φ`. -/
noncomputable def tensorProductMap {M N : ModuleCat.{uM} Rᵐᵒᵖ} (g : M ⟶ N) :
    tensorProductObj φ M →ₗ[Sᵐᵒᵖ] tensorProductObj φ N := by
  let sourceRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M
  let targetRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N
  let coefficientRCat := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  let sourceMap : sourceRCat →ₗ[R] targetRCat :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g).hom
  let coefficientId := @LinearMap.id R coefficientRCat _ _ coefficientRCat.isModule
  let tensorMap := @TensorProduct.map R R _ _ (RingHom.id R)
    sourceRCat coefficientRCat targetRCat coefficientRCat
    sourceRCat.isAddCommGroup.toAddCommMonoid
    coefficientRCat.isAddCommGroup.toAddCommMonoid
    targetRCat.isAddCommGroup.toAddCommMonoid
    coefficientRCat.isAddCommGroup.toAddCommMonoid
    sourceRCat.isModule coefficientRCat.isModule
    targetRCat.isModule coefficientRCat.isModule sourceMap coefficientId
  have pure (m : M) (s : S) :
      tensorMap (tensorProductTmul φ M m s) = tensorProductTmul φ N (g m) s :=
    @TensorProduct.map_tmul R R _ _ (RingHom.id R)
      sourceRCat coefficientRCat targetRCat coefficientRCat
      sourceRCat.isAddCommGroup.toAddCommMonoid
      coefficientRCat.isAddCommGroup.toAddCommMonoid
      targetRCat.isAddCommGroup.toAddCommMonoid
      coefficientRCat.isAddCommGroup.toAddCommMonoid
      sourceRCat.isModule coefficientRCat.isModule
      targetRCat.isModule coefficientRCat.isModule sourceMap coefficientId m s
  refine { toFun := tensorMap, map_add' := tensorMap.map_add, map_smul' := ?_ }
  intro t x
  refine @TensorProduct.inductionOn R _ M S
    sourceRCat.isAddCommGroup.toAddCommMonoid
    coefficientRCat.isAddCommGroup.toAddCommMonoid
    sourceRCat.isModule coefficientRCat.isModule
    (fun y ↦ tensorMap
        (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
          (tensorProductObj φ M).isModule.toSMul t y) =
      @SMul.smul Sᵐᵒᵖ (tensorProductObj φ N)
        (tensorProductObj φ N).isModule.toSMul t (tensorMap y)) x ?_ ?_
  · intro m s
    have sourceAction :
        @SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
          (tensorProductObj φ M).isModule.toSMul t (tensorProductTmul φ M m s) =
        tensorProductTmul φ M m (s * MulOpposite.unop t) := by
      simpa only [MulOpposite.op_unop] using
        tensorProductObj_smul_tmul φ M m s (MulOpposite.unop t)
    have targetAction :
        @SMul.smul Sᵐᵒᵖ (tensorProductObj φ N)
          (tensorProductObj φ N).isModule.toSMul t (tensorProductTmul φ N (g m) s) =
        tensorProductTmul φ N (g m) (s * MulOpposite.unop t) := by
      simpa only [MulOpposite.op_unop] using
        tensorProductObj_smul_tmul φ N (g m) s (MulOpposite.unop t)
    exact (congrArg tensorMap sourceAction).trans
      ((pure m (s * MulOpposite.unop t)).trans
        (targetAction.symm.trans
          (congrArg (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ N)
            (tensorProductObj φ N).isModule.toSMul t) (pure m s).symm)))
  · intro y z hy hz
    exact (congrArg tensorMap
      (@DistribMulAction.smul_add Sᵐᵒᵖ (tensorProductObj φ M) _
        (tensorProductObj φ M).isAddCommGroup.toAddCommMonoid.toAddMonoid
        (tensorProductObj φ M).isModule.toDistribMulAction t y z)).trans
      ((tensorMap.map_add _ _).trans
        ((congrArg₂ (fun a b : tensorProductObj φ N ↦ a + b) hy hz).trans
          ((@DistribMulAction.smul_add Sᵐᵒᵖ (tensorProductObj φ N) _
            (tensorProductObj φ N).isAddCommGroup.toAddCommMonoid.toAddMonoid
            (tensorProductObj φ N).isModule.toDistribMulAction t
            (tensorMap y) (tensorMap z)).symm.trans
            (congrArg (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ N)
              (tensorProductObj φ N).isModule.toSMul t) (tensorMap.map_add y z).symm))))

end RingTarget
end ModuleCat.RightExtension
end
