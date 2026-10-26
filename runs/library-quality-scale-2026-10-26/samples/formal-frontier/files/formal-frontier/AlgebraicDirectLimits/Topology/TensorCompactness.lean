/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Compact one-sided tensors

Finite generation of the algebraic coefficient module is the compactness
hypothesis for the one-sided tensor of a compact topological module. The
coefficient module needs neither a topology nor a basis. The scalar ring and
the two module carriers have independent universes.

A finite spanning family presents the tensor as a continuous image of a finite
power of the right factor. Surjectivity follows by tensoring the corresponding
algebraic surjection, while continuity follows from the fixed-coefficient
generators. No continuous coefficient coordinates are needed.

## References

The finite-generator tensor formulation follows the mathematical argument of
Formal Frontier Agents and uses the one-sided tensor and generator API of
Algebraic Direct Limits. Finite generation reuses Johan Commelin's Mathlib
development. Finite-free algebraic coordinates use Johannes Hölzl's standard
basis and Finsupp APIs and Jakob von Raumer's tensor-basis equivalence;
tensor-surjectivity uses Antoine Chambert-Loir's right-exactness development.
The continuous-linear API is due to Jan-David Salchow, Sébastien Gouëzel, Jean
Lo, Yury Kudryashov, Frédéric Dupuis and Heather Macbeth. The compact-space
predicate and continuous-image theorem reuse Mathlib's topology development by
Johannes Hölzl, Mario Carneiro and Yury Kudryashov.
-/

@[expose] public section

open scoped BigOperators TensorProduct

universe uR uC uM

namespace TensorProduct

universe uI

/-- A finite spanning family supplies all tensors by summing one tensor for each member. -/
private theorem surjective_sum_tmul_of_span_eq_top
    (R : Type uR) [CommSemiring R] (C : Type uC) (M : Type uM)
    [AddCommMonoid C] [AddCommMonoid M] [Module R C] [Module R M]
    {ι : Type uI} [Fintype ι] (c : ι → C)
    (hc : Submodule.span R (Set.range c) = ⊤) :
    Function.Surjective (fun x : ι → M ↦ ∑ i, c i ⊗ₜ[R] x i) := by
  classical
  let f : (ι → R) →ₗ[R] C := Module.piEquiv ι R C c
  have hf : Function.Surjective f :=
    (Module.surjective_piEquiv_apply_iff ι R C c).2 hc
  let e : TensorProduct R (ι → R) M ≃ₗ[R] (ι → M) :=
    (equivFinsuppOfBasisLeft (Pi.basisFun R ι)).trans
      (Finsupp.linearEquivFunOnFinite R M ι)
  have he (x : ι → M) :
      e.symm x = ∑ i, (Pi.basisFun R ι) i ⊗ₜ[R] x i := by
    dsimp only [e]
    rw [LinearEquiv.symm_trans_apply, equivFinsuppOfBasisLeft_symm_apply,
      Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.linearEquivFunOnFinite_symm_apply]
  have hsum (x : ι → M) :
      f.rTensor M (e.symm x) = ∑ i, c i ⊗ₜ[R] x i := by
    rw [he x, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.rTensor_tmul]
    exact congrArg (fun a : C ↦ a ⊗ₜ[R] x i)
      ((Pi.basisFun R ι).constr_basis R c i)
  have hsurj := (LinearMap.rTensor_surjective M (g := f) hf).comp e.symm.surjective
  intro z
  obtain ⟨x, hx⟩ := hsurj z
  exact ⟨x, (hsum x).symm.trans hx⟩

end TensorProduct

namespace TopModuleCat

universe uI

/-- The finite sum of tensor generators after the product projections. -/
private noncomputable def tensorGeneratorSum
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    {ι : Type uI} [Fintype ι] (c : ι → C) :
    (ι → M) →L[R] tensorLeftObj R C M :=
  ∑ i, (tensorGenerator R C M (c i)).comp
    (ContinuousLinearMap.proj (R := R) (φ := fun _ : ι ↦ (M : Type uM)) i)

/-- The finite-generator map evaluates as a sum of pure tensors. -/
private theorem tensorGeneratorSum_apply
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    {ι : Type uI} [Fintype ι] (c : ι → C) (x : ι → M) :
    tensorGeneratorSum R C M c x = ∑ i, c i ⊗ₜ[R] x i := by
  change @Eq (tensorLeftObj R C M) (tensorGeneratorSum R C M c x)
    (show tensorLeftObj R C M from ∑ i, c i ⊗ₜ[R] x i)
  have hSum : @Eq (tensorLeftObj R C M) (tensorGeneratorSum R C M c x)
      (∑ i, ((tensorGenerator R C M (c i)).comp
        (ContinuousLinearMap.proj (R := R) (φ := fun _ : ι ↦ (M : Type uM)) i)) x) :=
    sum_apply (β := tensorLeftObj R C M) Finset.univ _ x
  have hPure : @Eq (tensorLeftObj R C M)
      (∑ i, ((tensorGenerator R C M (c i)).comp
        (ContinuousLinearMap.proj (R := R) (φ := fun _ : ι ↦ (M : Type uM)) i)) x)
      (∑ i, (show tensorLeftObj R C M from c i ⊗ₜ[R] x i)) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
      tensorGenerator_apply R C M (c i) (x i)
  have hView : @Eq (tensorLeftObj R C M)
      (∑ i, (show tensorLeftObj R C M from c i ⊗ₜ[R] x i))
      (show tensorLeftObj R C M from ∑ i, c i ⊗ₜ[R] x i) := rfl
  exact @Eq.trans (tensorLeftObj R C M) _ _ _ hSum
    (@Eq.trans (tensorLeftObj R C M) _ _ _ hPure hView)

/-- Tensoring a compact topological module with a finitely generated algebraic
coefficient module preserves compactness for the one-sided tensor topology. -/
theorem compactSpace_tensorLeftObj (R : Type uR) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat.{uC} R) (M : TopModuleCat.{uM} R)
    [Module.Finite R C] [CompactSpace M] : CompactSpace (tensorLeftObj R C M) := by
  classical
  obtain ⟨n, c, hc⟩ := Module.Finite.exists_fin (R := R) (M := C)
  have hsurj : Function.Surjective (tensorGeneratorSum R C M c) := by
    intro z
    obtain ⟨x, hx⟩ := TensorProduct.surjective_sum_tmul_of_span_eq_top R C M c hc z
    exact ⟨x, (tensorGeneratorSum_apply R C M c x).trans hx⟩
  exact Function.Surjective.compactSpace (tensorGeneratorSum R C M c).continuous hsurj

end TopModuleCat
