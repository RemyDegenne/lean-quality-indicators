/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The module topology on finite-dimensional continuous duals

If a finite-dimensional vector space has the module topology, then its continuous dual,
with the topology of uniform convergence on bounded sets, also has the module topology.
The scalar field need not be complete. For a normed space over a nontrivially normed field,
`IsModuleTopology.strongDual` applies to its given topology; the dual topology is the
operator-norm topology.

## Implementation notes

Evaluation on a finite basis identifies the continuous dual with a finite product of copies
of the scalar field. The inverse is the finite sum of the continuous coordinate forms.
Continuity of this inverse follows from the module topology on the finite product, not
from a completeness assumption on the field. Empty bases are allowed.

The result is a theorem rather than a global instance, following the explicit use of
`isModuleTopologyOfFiniteDimensional`. It can be installed locally with
`letI := IsModuleTopology.strongDual 𝕜 E`.

## Credits

The proof uses the module-topology constructions of Kevin Buzzard and Will Sawin,
the finite-dimensional basis API of Mathlib, and the bounded-convergence topology of
Anatole Dedecker and Yury Kudryashov.
-/

@[expose] public section

noncomputable section

universe u v

namespace IsModuleTopology

variable (𝕜 : Type u) [NormedField 𝕜] (E : Type v)
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [FiniteDimensional 𝕜 E] [IsModuleTopology 𝕜 E]

/-- The continuous dual of a finite-dimensional vector space with the module topology has
the module topology for its topology of uniform convergence on bounded sets. No completeness
of the scalar field is required. -/
theorem strongDual : IsModuleTopology 𝕜 (StrongDual 𝕜 E) := by
  classical
  let b := Module.finBasis 𝕜 E
  let coord (i : Fin (Module.finrank 𝕜 E)) : StrongDual 𝕜 E :=
    ⟨b.coord i, IsModuleTopology.continuous_of_linearMap (b.coord i)⟩
  let e : StrongDual 𝕜 E ≃ₗ[𝕜] (Fin (Module.finrank 𝕜 E) → 𝕜) :=
    { toFun := fun φ i ↦ φ (b i)
      invFun := fun a ↦ ∑ i, a i • coord i
      left_inv := by
        intro φ
        apply ContinuousLinearMap.coe_injective
        apply b.ext
        intro i
        change (∑ j, φ (b j) • coord j) (b i) = φ (b i)
        simp [coord, Module.Basis.coord_apply, Finsupp.single_apply]
      right_inv := by
        intro a
        funext i
        change (∑ j, a j • coord j) (b i) = a i
        simp [coord, Module.Basis.coord_apply, Finsupp.single_apply]
      map_add' := by
        intro φ ψ
        ext i
        rfl
      map_smul' := by
        intro c φ
        ext i
        rfl }
  let ε : StrongDual 𝕜 E ≃L[𝕜] (Fin (Module.finrank 𝕜 E) → 𝕜) :=
    { e with
      continuous_toFun := continuous_pi fun i ↦ continuous_eval_const (b i)
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  exact IsModuleTopology.iso ε.symm

end IsModuleTopology
