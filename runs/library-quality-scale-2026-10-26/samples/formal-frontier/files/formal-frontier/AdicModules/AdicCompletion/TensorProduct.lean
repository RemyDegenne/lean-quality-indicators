/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Finiteness.Small

/-!
# Adic completion and tensor products

For a projective module over a commutative ring, the canonical comparison from tensoring with
the completed ring to the completed module is injective, for any ideal. If the module is also
finite, the comparison is bijective. The resulting equivalence is linear over the completed
ring, sends pure tensors to scalar multiples of the canonical map into the completion, and
agrees with Mathlib's Noetherian equivalence when both apply.

The proof detects coefficients in a free Finsupp module and uses a projective retraction and
naturality of the canonical comparison. Surjectivity for finite modules is reused from Mathlib.
No Noetherian hypothesis on the ring or finite-generation hypothesis on the ideal is needed.

## Implementation notes

The ring and module universes are independent. Only the agreement with Mathlib's Noetherian
equivalence uses a common universe, as required by that equivalence.

For a finite module over a commutative Noetherian ring, the same canonical comparison is
bijective without projectivity. The ring and module universes are independent, and the
common-universe comparison with Mathlib identifies the equivalence obtained by
`LinearEquiv.ofBijective` with Mathlib's finite-Noetherian equivalence.

## References

Mathlib's `RingTheory/AdicCompletion/AsTensorProduct.lean`, by Judith Ludwig and Christian Merten,
supplies the canonical comparison, its naturality, the finite-power comparison, finite-module
surjectivity, and the Noetherian equivalence. Mathlib's `Algebra/Module/Projective.lean`, by
Kevin Buzzard and Antoine Labelle, supplies the projective Finsupp retraction. Mathlib's
`LinearAlgebra/DirectSum/Finsupp.lean`, by Johannes Hölzl and Antoine Chambert-Loir, supplies
the tensor/Finsupp coefficient equivalence. Related finite-projective retraction results are
in Mathlib's `RingTheory/Finiteness/Projective.lean`, by Johan Commelin.
The independent-universe Noetherian comparison uses finite-module smallness from Mathlib's
`RingTheory/Finiteness/Small.lean`, by Antoine Chambert-Loir and María-Inés de Frutos-Fernández,
and the `Shrink` linear equivalence from Kim Morrison's module API.
-/

set_option warningAsError true

@[expose] public section

noncomputable section

universe uR uM uσ

open TensorProduct

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)

/-- The comparison for the scalar module agrees pointwise with the tensor right unitor. -/
private lemma ofTensorProduct_self_eq_rid_apply
    (x : AdicCompletion I R ⊗[R] R) :
    ofTensorProduct I R x =
      AlgebraTensorModule.rid R R (AdicCompletion I R) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a r =>
      rw [ofTensorProduct_tmul, AlgebraTensorModule.rid_tmul]
      apply AdicCompletion.ext
      intro n
      rw [smul_eval, of_apply, val_smul_apply]
      induction a.val n using Quotient.inductionOn' with
      | _ s =>
          change
            (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) (s * r)) =
              Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) (r * s)
          rw [mul_comm]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- A coefficient of the tensor/Finsupp equivalence is the completion of the corresponding
coefficient of the canonical comparison. -/
private lemma finsuppScalarRight_apply_eq_map_ofTensorProduct
    (σ : Type uσ) [DecidableEq σ]
    (x : AdicCompletion I R ⊗[R] (σ →₀ R)) (b : σ) :
    TensorProduct.finsuppScalarRight R R (AdicCompletion I R) σ x b =
      map I (Finsupp.lapply b : (σ →₀ R) →ₗ[R] R)
        (ofTensorProduct I (σ →₀ R) x) := by
  rw [TensorProduct.finsuppScalarRight_apply, ← ofTensorProduct_self_eq_rid_apply I]
  rw [← LinearMap.baseChange_eq_ltensor]
  exact (LinearMap.congr_fun
    (ofTensorProduct_naturality I (Finsupp.lapply b : (σ →₀ R) →ₗ[R] R)) x).symm

/-- The canonical tensor comparison is injective on an arbitrary Finsupp module. -/
private theorem ofTensorProduct_injective_finsupp (σ : Type uσ) :
    Function.Injective (ofTensorProduct I (σ →₀ R)) := by
  classical
  intro x y hxy
  apply (TensorProduct.finsuppScalarRight R R (AdicCompletion I R) σ).injective
  apply Finsupp.ext
  intro b
  rw [finsuppScalarRight_apply_eq_map_ofTensorProduct I σ x b,
    finsuppScalarRight_apply_eq_map_ofTensorProduct I σ y b, hxy]

variable (M : Type uM) [AddCommGroup M] [Module R M]

/-- For a projective module over a commutative ring, the canonical comparison from tensoring
with the completed ring to the completed module is injective, for any ideal. -/
theorem ofTensorProduct_injective_of_projective
    [Module.Projective R M] :
    Function.Injective (ofTensorProduct I M) := by
  obtain ⟨g, hfg⟩ := (Module.projective_def' (R := R) (P := M)).mp inferInstance
  have hsplit :
      (Finsupp.linearCombination R id).baseChange (AdicCompletion I R) ∘ₗ
          g.baseChange (AdicCompletion I R) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_id]
  have hg := LinearMap.injective_of_comp_eq_id _ _ hsplit
  intro x y hxy
  apply hg
  apply ofTensorProduct_injective_finsupp I M
  calc
    ofTensorProduct I (M →₀ R) (g.baseChange (AdicCompletion I R) x) =
        map I g (ofTensorProduct I M x) :=
      (LinearMap.congr_fun (ofTensorProduct_naturality I g) x).symm
    _ = map I g (ofTensorProduct I M y) := congrArg (map I g) hxy
    _ = ofTensorProduct I (M →₀ R) (g.baseChange (AdicCompletion I R) y) :=
      LinearMap.congr_fun (ofTensorProduct_naturality I g) y

/-- For a finite projective module, tensoring with the completed ring gives its adic completion.
The canonical comparison is bijective over an arbitrary commutative ring and for any ideal,
by projective injectivity and finite-module surjectivity. -/
theorem ofTensorProduct_bijective_of_finite_of_projective
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (ofTensorProduct I M) :=
  ⟨ofTensorProduct_injective_of_projective I M,
    ofTensorProduct_surjective_of_finite I M⟩

/-- The canonical tensor comparison as an equivalence over the completed ring for a finite
projective module. -/
noncomputable def ofTensorProductEquivOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finite_of_projective I M)

/-- The finite-projective equivalence has the canonical tensor comparison as its linear map. -/
@[simp]
theorem coe_ofTensorProductEquivOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] :
    (ofTensorProductEquivOfFiniteProjective I M).toLinearMap = ofTensorProduct I M :=
  rfl

/-- The finite-projective equivalence sends a pure tensor to the corresponding scalar multiple
in the completed module. -/
@[simp]
theorem ofTensorProductEquivOfFiniteProjective_apply
    [Module.Finite R M] [Module.Projective R M] (a : AdicCompletion I R) (m : M) :
    ofTensorProductEquivOfFiniteProjective I M (a ⊗ₜ[R] m) = a • of I M m :=
  ofTensorProduct_tmul I M a m

/-- The inverse finite-projective equivalence sends a canonical module element to its tensor
with one. -/
@[simp]
theorem ofTensorProductEquivOfFiniteProjective_symm_of
    [Module.Finite R M] [Module.Projective R M] (m : M) :
    (ofTensorProductEquivOfFiniteProjective I M).symm (of I M m) =
      (1 : AdicCompletion I R) ⊗ₜ[R] m := by
  apply (ofTensorProductEquivOfFiniteProjective I M).injective
  simp

/-- For a finite module over a commutative Noetherian ring, the canonical comparison from
tensoring with the completed ring to the completed module is bijective for every ideal.
This generalizes the finite-Noetherian comparison of Judith Ludwig and Christian Merten in
Mathlib to independent ring and module universes. -/
theorem ofTensorProduct_bijective [IsNoetherianRing R] [Module.Finite R M] :
    Function.Bijective (ofTensorProduct I M) := by
  have : Small.{uR} M := Module.Finite.small R M
  let e : M ≃ₗ[R] Shrink.{uR} M := (Shrink.linearEquiv R M).symm
  let : Module.Finite R (Shrink.{uR} M) := Module.Finite.equiv e
  have hc := ofTensorProduct_bijective_of_finite_of_isNoetherian I (Shrink.{uR} M)
  have he : Function.Bijective (map I e.toLinearMap) := (congr I e).bijective
  apply (Function.Bijective.of_comp_iff' he _).mp
  change Function.Bijective (map I e.toLinearMap ∘ₗ ofTensorProduct I M)
  rw [ofTensorProduct_naturality]
  exact hc.comp (e.baseChange R (AdicCompletion I R) _ _).bijective

section Noetherian

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable (M : Type uR) [AddCommGroup M] [Module R M]

/-- When the ring is Noetherian, the finite-projective equivalence agrees with Mathlib's
finite-module Noetherian equivalence: both have the same canonical underlying map. -/
theorem ofTensorProductEquivOfFiniteProjective_eq_ofFiniteNoetherian
    [Module.Finite R M] [Module.Projective R M] [IsNoetherianRing R] :
    ofTensorProductEquivOfFiniteProjective I M = ofTensorProductEquivOfFiniteNoetherian I M := by
  ext x
  rfl

/-- Mathlib's finite-Noetherian equivalence is the equivalence obtained from the canonical
completed-ring-linear comparison and its bijectivity. -/
theorem ofTensorProductEquivOfFiniteNoetherian_eq_ofBijective
    [IsNoetherianRing R] [Module.Finite R M] :
    ofTensorProductEquivOfFiniteNoetherian I M =
      LinearEquiv.ofBijective (ofTensorProduct I M) (ofTensorProduct_bijective I M) := by
  apply LinearEquiv.ext
  intro x
  exact ofTensorProductEquivOfFiniteNoetherian_apply I M x

end Noetherian

end AdicCompletion
