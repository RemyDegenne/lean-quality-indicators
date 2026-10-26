/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import ProjectiveModules.Invertible.Endomorphism

/-!
# Topology and continuous endomorphisms of invertible modules

A Hausdorff invertible topological vector space over a nontrivially normed field has
its module topology. The result concerns the given topology and module structure;
it requires neither completeness of the field nor a norm on the vector space.

An algebraic linear coordinate has zero kernel. Hausdorffness makes this kernel
closed, so Mathlib's closed-kernel continuity theorem applies even over an
incomplete field. The inverse coordinate is continuous by the scalar field's
module topology, and the resulting continuous linear equivalence transports that
property to the original space.

Scalar multiplication also gives `ContinuousLinearMap.scalarEndEquiv`, a continuous
linear equivalence from the field to the continuous endomorphisms of the line,
with their topology of bounded convergence. Its inverse is the canonical
algebraic inverse from `Module.Invertible.toModuleEndRingEquiv`, applied after
forgetting continuity. The inverse linear form has closed zero kernel, so the
same closed-kernel criterion proves its continuity.

Neither construction changes the given topology. The scalar endomorphism
equivalence requires no input vector, frame, inverse, completeness or norm on the
line. Its characteristic API describes scalar action on every vector, recovers
the algebraic scalar endomorphism map and agrees with Mathlib's
`ContinuousLinearMap.toSpanSingletonCLE` on the scalar field itself.

## References

* Mathlib, `RingTheory.PicardGroup`, for invertible modules and their algebraic
  coordinate equivalences.
* Mathlib, `Topology.Algebra.Module.FiniteDimension` and
  `Topology.Algebra.Module.ModuleTopology`, for closed-kernel continuity and
  transport of module topologies.
* Mathlib, `Topology.Algebra.Module.Spaces.ContinuousLinearMap`, for homotheties,
  the scalar-field equivalence and the topology of bounded convergence.
* Projective Modules, `Invertible.Endomorphism`, for the canonical algebraic
  scalar endomorphism equivalence, contributed by Prism.
* Formal Frontier Agents, formalization of the Hausdorff line argument and
  continuous scalar endomorphism equivalence.
-/

@[expose] public section

universe uκ uE

noncomputable section

namespace Module.Invertible

/-- A Hausdorff invertible topological module over a nontrivially normed field carries
the module topology on its given topological space. -/
theorem isModuleTopology (κ : Type uκ) [NontriviallyNormedField κ]
    (E : Type uE) [AddCommGroup E] [Module κ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul κ E] [T2Space E] [Module.Invertible κ E] :
    IsModuleTopology κ E := by
  let e : E ≃ₗ[κ] κ :=
    ((Module.Invertible.free_iff_linearEquiv (R := κ) (M := E)).mp inferInstance).some
  have hker : LinearMap.ker e.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
  have he : Continuous e := e.toLinearMap.continuous_of_isClosed_ker (by
    simpa only [hker, Submodule.bot_coe] using
      (isClosed_singleton : IsClosed ({(0 : E)} : Set E)))
  let eL : E ≃L[κ] κ :=
    { toLinearEquiv := e
      continuous_toFun := he
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  exact IsModuleTopology.iso eL.symm

end Module.Invertible

namespace ContinuousLinearMap

section Homothety

variable (κ : Type uκ) [NormedField κ]
  (E : Type uE) [AddCommGroup E] [Module κ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul κ E]

/-- The continuous homothety family agrees with the algebraic scalar endomorphism map. -/
theorem toSpanSingleton_id_eq_toModuleEndRingEquiv [Module.Invertible κ E] (a : κ) :
    (toSpanSingleton κ (ContinuousLinearMap.id κ E) a).toLinearMap =
      Module.Invertible.toModuleEndRingEquiv κ E a := by
  ext v
  rfl

end Homothety

section ScalarEnd

variable (κ : Type uκ) [NontriviallyNormedField κ]
  (E : Type uE) [AddCommGroup E] [Module κ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul κ E]

/-- Scalar multiplication as a continuous linear equivalence with the continuous
endomorphisms of a Hausdorff line over a nontrivially normed field. No vector, frame,
or inverse is part of the input. -/
noncomputable def scalarEndEquiv [T2Space E] [Module.Invertible κ E] : κ ≃L[κ] (E →L[κ] E) := by
  let s := toSpanSingleton κ (ContinuousLinearMap.id κ E)
  let r := Module.Invertible.toModuleEndRingEquiv κ E
  let e : κ ≃ₗ[κ] (E →L[κ] E) :=
    { s.toLinearMap with
      invFun := fun A ↦ r.symm A.toLinearMap
      left_inv := fun a ↦ r.symm_apply_apply a
      right_inv := fun A ↦ by
        ext v
        exact DFunLike.congr_fun (r.apply_symm_apply A.toLinearMap) v }
  -- The inverse is a linear form on the Hausdorff space of continuous endomorphisms.
  -- Its zero kernel is closed, so no norm or completeness on E is needed.
  have hker : LinearMap.ker e.symm.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr e.symm.injective
  exact
    { e with
      continuous_toFun := s.continuous
      continuous_invFun := e.symm.toLinearMap.continuous_of_isClosed_ker (by
        simpa only [hker, Submodule.bot_coe] using
          (isClosed_singleton : IsClosed ({(0 : E →L[κ] E)} : Set (E →L[κ] E)))) }

variable [T2Space E] [Module.Invertible κ E]

/-- The forward continuous linear map is the homothety family. -/
@[simp]
theorem scalarEndEquiv_toContinuousLinearMap :
    (scalarEndEquiv κ E).toContinuousLinearMap =
      toSpanSingleton κ (ContinuousLinearMap.id κ E) := by
  rfl

/-- The endomorphism associated to a scalar acts by scalar multiplication. -/
@[simp]
theorem scalarEndEquiv_apply (a : κ) (v : E) :
    scalarEndEquiv κ E a v = a • v := by
  rfl

/-- Forgetting continuity recovers the canonical algebraic scalar endomorphism map. -/
theorem scalarEndEquiv_toLinearMap (a : κ) :
    (scalarEndEquiv κ E a).toLinearMap =
      Module.Invertible.toModuleEndRingEquiv κ E a := by
  ext v
  exact scalarEndEquiv_apply κ E a v

/-- The inverse scalar reproduces the endomorphism on every vector of the line. -/
theorem scalarEndEquiv_symm_smul (A : E →L[κ] E) (v : E) :
    (scalarEndEquiv κ E).symm A • v = A v := by
  rw [← scalarEndEquiv_apply κ E, (scalarEndEquiv κ E).apply_symm_apply]

end ScalarEnd

variable (κ : Type uκ) [NontriviallyNormedField κ]

/-- On the scalar field itself, the scalar endomorphism equivalence is
`ContinuousLinearMap.toSpanSingletonCLE`. -/
theorem scalarEndEquiv_self :
    scalarEndEquiv κ κ = (toSpanSingletonCLE : κ ≃L[κ] (κ →L[κ] κ)) := by
  apply DFunLike.ext
  intro a
  apply DFunLike.ext
  intro v
  change scalarEndEquiv κ κ a v = v * a
  exact (scalarEndEquiv_apply κ κ a v).trans (mul_comm a v)

end ContinuousLinearMap
