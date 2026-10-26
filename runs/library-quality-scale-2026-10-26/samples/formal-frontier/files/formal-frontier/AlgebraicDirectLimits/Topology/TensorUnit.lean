/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The scalar unit for the one-sided tensor topology

`TopModuleCat.tensorUnitContinuousLinearEquiv` equips Mathlib's algebraic
`TensorProduct.lid R M` with the continuity data for the one-sided tensor topology
on `R ⊗[R] M` and the supplied topology on `M`. Its forward map sends `r ⊗ₜ m`
to `r • m`, and its inverse is the continuous tensor generator at `1`.

The left factor is the algebraic object `ModuleCat.of R R`, not a topological
module. The scalar ring carries a supplied topology, and the right factor supplies
jointly continuous scalar multiplication. No continuity of ring multiplication,
module-topology equality, finite basis, separation or nontriviality is required.
The ring and right-factor carrier universes are independent.

## Implementation notes

The underlying linear equivalence is exactly Mathlib's `TensorProduct.lid`.
Forward continuity is tested on the existing fixed-coefficient generators:
for fixed `r`, the composite is the continuous map `m ↦ r • m`. The inverse is
`TopModuleCat.tensorGenerator` at `1`. There is no new tensor topology or
algebraic unit construction. Naturality uses the existing `tensorMapCLM`.

## References

The algebraic tensor unit and its inverse are Mathlib's constructions by Kenny Lau
and Mario Carneiro. The one-sided tensor topology and linear continuity criterion
are those of `AlgebraicDirectLimits.Topology.TensorProduct` and
`AlgebraicDirectLimits.Topology.Coinduced`, following the Continuous Group Cohomology
formalization by Formal Frontier Agents, including Beacon's original topological
development. Mathlib's topological-module and coinduced constructions are due to
Richard Hill and Andrew Yang. The continuous-linear-equivalence API is due to
Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis
and Heather Macbeth.
-/

@[expose] public section

open scoped TensorProduct

universe uR uM uN

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]

/-- Mathlib's scalar tensor identity with the one-sided tensor topology and the
supplied topology on the right factor. The scalar factor is purely algebraic. -/
noncomputable def tensorUnitContinuousLinearEquiv (M : TopModuleCat.{uM} R) :
    tensorLeftObj R (ModuleCat.of R R) M ≃L[R] M where
  toLinearEquiv := TensorProduct.lid R M
  continuous_toFun := by
    apply (continuous_tensorLeftObj_iff_tmul R (ModuleCat.of R R) M M
      (show tensorLeftObj R (ModuleCat.of R R) M →ₗ[R] M from
        (TensorProduct.lid R M).toLinearMap)).mpr
    intro r
    change Continuous (fun m : M ↦ r • m)
    exact continuous_const_smul r
  continuous_invFun := by
    change Continuous (tensorGenerator R (ModuleCat.of R R) M (1 : R))
    exact (tensorGenerator R (ModuleCat.of R R) M (1 : R)).continuous

/-- Forgetting continuity gives exactly Mathlib's algebraic scalar tensor unit. -/
@[simp]
theorem tensorUnitContinuousLinearEquiv_toLinearEquiv (M : TopModuleCat.{uM} R) :
    (tensorUnitContinuousLinearEquiv R M).toLinearEquiv = TensorProduct.lid R M := rfl

/-- The underlying linear map is Mathlib's scalar tensor unit map. -/
@[simp]
theorem tensorUnitContinuousLinearEquiv_toLinearMap (M : TopModuleCat.{uM} R) :
    (tensorUnitContinuousLinearEquiv R M).toContinuousLinearMap.toLinearMap =
      (TensorProduct.lid R M).toLinearMap := rfl

/-- On every tensor, the continuous unit agrees with the algebraic unit. -/
theorem tensorUnitContinuousLinearEquiv_apply (M : TopModuleCat.{uM} R)
    (x : tensorLeftObj R (ModuleCat.of R R) M) :
    tensorUnitContinuousLinearEquiv R M x = TensorProduct.lid R M x := by
  rfl

/-- The scalar tensor unit sends a pure tensor to scalar multiplication. -/
@[simp]
theorem tensorUnitContinuousLinearEquiv_tmul (M : TopModuleCat.{uM} R) (r : R) (m : M) :
    tensorUnitContinuousLinearEquiv R M (r ⊗ₜ[R] m) = r • m := by
  rfl

/-- The inverse scalar tensor unit sends `m` to `1 ⊗ₜ m`. -/
@[simp]
theorem tensorUnitContinuousLinearEquiv_symm_apply (M : TopModuleCat.{uM} R) (m : M) :
    (tensorUnitContinuousLinearEquiv R M).symm m = (1 : R) ⊗ₜ[R] m := by
  rfl

/-- The inverse continuous linear map is the existing tensor generator at `1`. -/
@[simp]
theorem tensorUnitContinuousLinearEquiv_symm_toContinuousLinearMap
    (M : TopModuleCat.{uM} R) :
    (tensorUnitContinuousLinearEquiv R M).symm.toContinuousLinearMap =
      tensorGenerator R (ModuleCat.of R R) M (1 : R) := by
  ext m
  rfl

/-- A fixed-coefficient tensor generator is evaluated by scalar multiplication. -/
@[simp]
theorem tensorUnitContinuousLinearEquiv_tensorGenerator_apply
    (M : TopModuleCat.{uM} R) (r : R) (m : M) :
    tensorUnitContinuousLinearEquiv R M
      (tensorGenerator R (ModuleCat.of R R) M r m) = r • m := by
  exact (congrArg (tensorUnitContinuousLinearEquiv R M)
    (tensorGenerator_apply R (ModuleCat.of R R) M r m)).trans
      (tensorUnitContinuousLinearEquiv_tmul R M r m)

/-- Composing the scalar tensor unit with a generator gives the scalar multiple
of the identity continuous linear map. -/
theorem tensorUnitContinuousLinearEquiv_comp_tensorGenerator
    (M : TopModuleCat.{uM} R) (r : R) :
    (tensorUnitContinuousLinearEquiv R M).toContinuousLinearMap.comp
      (tensorGenerator R (ModuleCat.of R R) M r) =
        r • ContinuousLinearMap.id R M := by
  apply ContinuousLinearMap.ext
  intro m
  calc
    _ = tensorUnitContinuousLinearEquiv R M
        (tensorGenerator R (ModuleCat.of R R) M r m) :=
      (ContinuousLinearMap.comp_apply
        (tensorUnitContinuousLinearEquiv R M).toContinuousLinearMap
        (tensorGenerator R (ModuleCat.of R R) M r) m).trans
          (ContinuousLinearEquiv.coe_apply (tensorUnitContinuousLinearEquiv R M) _)
    _ = r • m := tensorUnitContinuousLinearEquiv_tensorGenerator_apply R M r m
    _ = _ := (smul_apply (ContinuousLinearMap.id R M) r m).symm

/-- Pure-tensor evaluation uniquely determines the continuous scalar tensor unit. -/
theorem tensorUnitContinuousLinearEquiv_unique (M : TopModuleCat.{uM} R)
    (e : tensorLeftObj R (ModuleCat.of R R) M ≃L[R] M)
    (he : ∀ (r : R) (m : M), e (r ⊗ₜ[R] m) = r • m) :
    e = tensorUnitContinuousLinearEquiv R M := by
  apply ContinuousLinearEquiv.coe_injective
  apply tensorLeft_ext R
  intro r m
  exact (he r m).trans (tensorUnitContinuousLinearEquiv_tmul R M r m).symm

/-- The scalar tensor unit commutes with any continuous linear map on the right
factor, including maps between independently leveled carriers. -/
theorem tensorUnitContinuousLinearEquiv_naturality
    {M : TopModuleCat.{uM} R} {N : TopModuleCat.{uN} R} (g : M →L[R] N) :
    (tensorUnitContinuousLinearEquiv R N).toContinuousLinearMap.comp
      (tensorMapCLM R (LinearMap.id : (ModuleCat.of R R) →ₗ[R] (ModuleCat.of R R)) g) =
        g.comp (tensorUnitContinuousLinearEquiv R M).toContinuousLinearMap := by
  apply tensorLeft_ext R
  intro r m
  calc
    _ = tensorUnitContinuousLinearEquiv R N
        (tensorMapCLM R (LinearMap.id : (ModuleCat.of R R) →ₗ[R] (ModuleCat.of R R)) g
          (r ⊗ₜ[R] m)) :=
      (ContinuousLinearMap.comp_apply
        (tensorUnitContinuousLinearEquiv R N).toContinuousLinearMap
        (tensorMapCLM R (LinearMap.id : (ModuleCat.of R R) →ₗ[R] (ModuleCat.of R R)) g)
        (show tensorLeftObj R (ModuleCat.of R R) M from r ⊗ₜ[R] m)).trans
          (ContinuousLinearEquiv.coe_apply (tensorUnitContinuousLinearEquiv R N) _)
    _ = tensorUnitContinuousLinearEquiv R N (r ⊗ₜ[R] g m) :=
      congrArg (tensorUnitContinuousLinearEquiv R N)
        (tensorMapCLM_tmul R
          (LinearMap.id : (ModuleCat.of R R) →ₗ[R] (ModuleCat.of R R)) g r m)
    _ = r • g m := tensorUnitContinuousLinearEquiv_tmul R N r (g m)
    _ = g (r • m) := (g.map_smul r m).symm
    _ = g (tensorUnitContinuousLinearEquiv R M (r ⊗ₜ[R] m)) :=
      congrArg g (tensorUnitContinuousLinearEquiv_tmul R M r m).symm
    _ = _ :=
      ((ContinuousLinearMap.comp_apply g
        (tensorUnitContinuousLinearEquiv R M).toContinuousLinearMap
        (show tensorLeftObj R (ModuleCat.of R R) M from r ⊗ₜ[R] m)).trans
          (congrArg g
            (ContinuousLinearEquiv.coe_apply (tensorUnitContinuousLinearEquiv R M) _))).symm

end TopModuleCat
