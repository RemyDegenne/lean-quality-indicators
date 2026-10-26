/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.Basic

/-!
# Cyclicity and commutator traces of finite projective modules

For linear maps in opposite directions between two finite projective modules
over a commutative semiring, the traces of their composites agree. The module
carriers may inhabit independent universes, and neither freeness nor additive
inverses are required.

When the module is an additive commutative group, the trace of an additive
commutator of endomorphisms `f.comp g - g.comp f` is zero. This needs no ring
structure on the scalar semiring: additivity and cyclicity suffice, without
subtracting trace values.

The cyclicity proof represents one map through the canonical dual tensor–Hom
equivalence and reduces by tensor induction to the rank-one trace formula.

## References

The tensor description and evaluation formulas used here are from the
formalization by Oliver Nash and Antoine Labelle in
`Mathlib.LinearAlgebra.Contraction`.
-/

@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace LinearMap

variable (R : Type uR) [CommSemiring R]
variable (M : Type uM) [AddCommMonoid M] [Module R M]
variable (N : Type uN) [AddCommMonoid N] [Module R N]

/-- The traces of the two composites of maps between finite projective modules agree. -/
theorem traceOfFiniteProjective_comp_comm
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    traceOfFiniteProjective R M (g.comp f) =
      traceOfFiniteProjective R N (f.comp g) := by
  obtain ⟨t, rfl⟩ := (dualTensorHom_bijective (R := R) (M := M) (N := N)).2 f
  induction t using TensorProduct.inductionOn with
  | tmul φ y =>
      have h₁ : g.comp (dualTensorHom R M N (φ ⊗ₜ[R] y)) =
          φ.smulRight (g y) := by
        apply LinearMap.ext
        intro x
        change g (φ x • y) = φ x • g y
        exact g.map_smul _ _
      have h₂ : (dualTensorHom R M N (φ ⊗ₜ[R] y)).comp g =
          (φ.comp g).smulRight y := by
        apply LinearMap.ext
        intro x
        rfl
      simp only [h₁, h₂, traceOfFiniteProjective_smulRight, comp_apply]
  | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, comp_add, add_comp, h₁, h₂]

/-- The trace of an additive commutator on a finite projective module is zero.

Additive inverses are required only in the module, not in the scalar semiring. -/
theorem traceOfFiniteProjective_commutator
    (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (f g : M →ₗ[R] M) :
    traceOfFiniteProjective R M (f.comp g - g.comp f) = 0 := by
  calc
    traceOfFiniteProjective R M (f.comp g - g.comp f) =
        traceOfFiniteProjective R M (f.comp g) +
          traceOfFiniteProjective R M (-(g.comp f)) := by
      rw [sub_eq_add_neg, map_add]
    _ = traceOfFiniteProjective R M (g.comp f) +
          traceOfFiniteProjective R M (-(g.comp f)) := by
      rw [traceOfFiniteProjective_comp_comm R M M g f]
    _ = traceOfFiniteProjective R M (g.comp f - g.comp f) := by
      rw [sub_eq_add_neg, map_add]
    _ = 0 := by rw [sub_self, map_zero]

end LinearMap
