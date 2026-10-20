@[expose] public section

@[simp]
theorem lequivProdOfRightSplitExact_apply
    {R X A B : Type*} [Ring R]
    [AddCommGroup X] [AddCommGroup B] [AddCommGroup A]
    [Module R X] [Module R B] [Module R A]
    {j : X →ₗ[R] A} {f : A →ₗ[R] B} {g : B →ₗ[R] A}
    (hj : Function.Injective j) (hexac : LinearMap.range j = LinearMap.ker f)
    (hfg : f.comp g = LinearMap.id) (x : X) (b : B) :
    _root_.lequivProdOfRightSplitExact (j := j) (g := f) (f := g) hj hexac hfg
      (x, b) = j x + g b := by
  -- The universe lifts preserve the given section, and the inverse of the
  -- splitting isomorphism is the biproduct descendent of `j` and `g`.
  change
    ((CategoryTheory.CategoryStruct.comp (ModuleCat.biprodIsoProd _ _).inv
      (CategoryTheory.Limits.biprod.desc
        (ModuleCat.ofHom
          (ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap))
        (ModuleCat.ofHom
          (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap)))).hom
      (ULift.up x, ULift.up b)).down = j x + g b
  rw [CategoryTheory.Limits.biprod.desc_eq, CategoryTheory.Preadditive.comp_add]
  simp only [← CategoryTheory.Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
    ModuleCat.biprodIsoProd_inv_comp_snd, ModuleCat.hom_add, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearEquiv.coe_toLinearMap,
    ULift.moduleEquiv_apply, ULift.moduleEquiv_symm_apply]
  rfl

end
