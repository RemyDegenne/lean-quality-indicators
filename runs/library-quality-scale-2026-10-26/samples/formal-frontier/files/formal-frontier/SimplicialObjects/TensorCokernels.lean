/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorMaps
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Cokernels of tensor-chain maps

The natural comparison between integral tensor chains and normalized chains with
lifted coefficients induces a natural isomorphism between their cokernel diagrams
on the entire arrow category of simplicial sets. Its components agree with
`CategoryTheory.Limits.cokernel.mapIso` for the original chain comparisons, and
its forward and inverse maps are characterized by the cokernel projections.

These are cokernels in the category of chain complexes, not homology groups.
No monomorphism, flatness, finiteness or nontriviality hypothesis is needed.
The coefficient, simplex and padding universes remain independent.

## References

* `SimplicialObjects.TensorCoefficients` and `SimplicialObjects.TensorMaps`
  supply the tensor complexes, their comparisons and the natural isomorphism.
* Mathlib supplies `Functor.mapArrowFunctor`, `Functor.isoWhiskerRight`, `Limits.coker`
  and `Limits.cokernel.mapIso`. Colimits of complexes are supplied degreewise by
  Mathlib's homological-complex colimit construction.
-/

@[expose] public section

universe a w p

open CategoryTheory Limits

namespace SSet

/-- The natural comparison between cokernels of tensor-chain maps and cokernels
of normalized-chain maps with lifted coefficients, for all simplicial arrows. -/
noncomputable def tensorNormalizedChainCokerNatIso (A : Type a) [AddCommGroup A] :
    (tensorNormalizedChainComplexFunctor.{a, w, p} A).mapArrow ⋙ coker _ ≅
      (normalizedChainComplexFunctorObj
        (ModuleCat.of ℤ (ULift.{max w p} A))).mapArrow ⋙ coker _ :=
  Functor.isoWhiskerRight
    ((Functor.mapArrowFunctor SSet.{w} (ChainComplex (ModuleCat.{max a w p} ℤ) ℕ)).mapIso
      (tensorNormalizedChainNatIso.{a, w, p} A)) (coker _)

/-- The forward cokernel comparison intertwines the projections by the target
chain comparison. -/
@[reassoc (attr := simp)]
theorem cokernel_π_tensorNormalizedChainCokerNatIso_hom_app
    (A : Type a) [AddCommGroup A] {S T : SSet.{w}} (f : S ⟶ T) :
    cokernel.π ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f) ≫
        (tensorNormalizedChainCokerNatIso.{a, w, p} A).hom.app (Arrow.mk f) =
      (tensorNormalizedChainIso.{a, w, p} A T).hom ≫
        cokernel.π (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))) := by
  have h :=
    ((coker.π (ChainComplex (ModuleCat.{max a w p} ℤ) ℕ)).naturality
      (((Functor.mapArrowFunctor SSet.{w} (ChainComplex (ModuleCat.{max a w p} ℤ) ℕ)).map
        (tensorNormalizedChainNatIso.{a, w, p} A).hom).app (Arrow.mk f))).symm
  -- Normalize the arrow endpoints in the characteristic equality.
  change
    (cokernel.π ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f) ≫
        (tensorNormalizedChainCokerNatIso.{a, w, p} A).hom.app (Arrow.mk f) :
      tensorNormalizedChainComplex.{a, w, p} A T ⟶
        cokernel (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A)))) =
      (tensorNormalizedChainIso.{a, w, p} A T).hom ≫
        cokernel.π (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))) at h
  exact h

/-- The inverse cokernel comparison intertwines the projections by the inverse
target chain comparison. -/
@[reassoc (attr := simp)]
theorem cokernel_π_tensorNormalizedChainCokerNatIso_inv_app
    (A : Type a) [AddCommGroup A] {S T : SSet.{w}} (f : S ⟶ T) :
    cokernel.π (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))) ≫
        (tensorNormalizedChainCokerNatIso.{a, w, p} A).inv.app (Arrow.mk f) =
      (tensorNormalizedChainIso.{a, w, p} A T).inv ≫
        cokernel.π ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f) := by
  have h :=
    ((coker.π (ChainComplex (ModuleCat.{max a w p} ℤ) ℕ)).naturality
      (((Functor.mapArrowFunctor SSet.{w} (ChainComplex (ModuleCat.{max a w p} ℤ) ℕ)).map
        (tensorNormalizedChainNatIso.{a, w, p} A).inv).app (Arrow.mk f))).symm
  -- Normalize the arrow endpoints in the characteristic equality.
  change
    (cokernel.π (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))) ≫
        (tensorNormalizedChainCokerNatIso.{a, w, p} A).inv.app (Arrow.mk f) :
      T.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A)) ⟶
        cokernel ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f)) =
      (tensorNormalizedChainIso.{a, w, p} A T).inv ≫
        cokernel.π ((tensorNormalizedChainComplexFunctor.{a, w, p} A).map f) at h
  exact h

/-- Each component is the cokernel isomorphism induced by the original chain
comparisons and their naturality square. -/
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
