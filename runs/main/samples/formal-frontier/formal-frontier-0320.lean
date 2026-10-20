@[expose] public section

universe a w p

open CategoryTheory Limits

namespace SSet

@[simp]
theorem tensorNormalizedChainCokerNatIso_app
    (A : Type a) [AddCommGroup A] {S T : SSet.{w}} (f : S ⟶ T) :
    (tensorNormalizedChainCokerNatIso.{a, w, p} A).app (Arrow.mk f) =
      cokernel.mapIso
        ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f)
        (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A)))
        (tensorNormalizedChainIso.{a, w, p} A S)
        (tensorNormalizedChainIso.{a, w, p} A T)
        (tensorNormalizedChainIso_hom_naturality.{a, w, p} A f).symm := by
  -- Precompose the original hom equality instead of rewriting the dependent isomorphism.
  have hπ := congrArg
    (fun k :
      cokernel ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f) ⟶
        cokernel (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))) ↦
      cokernel.π ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f) ≫ k)
    (cokernel.mapIso_hom
      ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f)
      (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A)))
      (tensorNormalizedChainIso.{a, w, p} A S)
      (tensorNormalizedChainIso.{a, w, p} A T)
      (tensorNormalizedChainIso_hom_naturality.{a, w, p} A f).symm)
  apply Iso.ext
  refine (Iso.app_hom _ _).trans ?_
  apply (cancel_epi (cokernel.π
    ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f))).mp
  exact (cokernel_π_tensorNormalizedChainCokerNatIso_hom_app.{a, w, p} A f).trans
    (hπ.trans (cokernel.π_desc
      ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f)
      ((tensorNormalizedChainIso.{a, w, p} A T).hom ≫
        cokernel.π (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A)))) _)).symm

end SSet
end
