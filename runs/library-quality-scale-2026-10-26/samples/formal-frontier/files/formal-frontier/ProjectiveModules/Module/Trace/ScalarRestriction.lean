/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.ScalarRestriction
public import ProjectiveModules.Module.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs

import ProjectiveModules.Module.Trace.Comparison
import ProjectiveModules.Module.Trace.Cyclicity

/-!
# Finite-projective trace under restriction of scalars

For a tower of commutative semirings `R → A`, with `A` finite projective over
`R` and `M` finite projective over `A`, the `R`-trace of an `A`-linear
endomorphism restricted to `R` is the `R`-trace of multiplication on `A` by its
`A`-trace. The scalar and module carriers may inhabit independent universes.
Neither freeness nor additive inverses are required.

On a finite free tower of commutative rings, specialization to multiplication
by an algebra element agrees with the symmetry of `Algebra.trace_trace`.

## Implementation notes

Restriction retains the given compatible `R`-action on `M`. The restricted
trace receives its finiteness and projectivity arguments from
`Module.Finite.trans` and `Module.Projective.trans`, respectively.

## References

The algebra-element tower trace is formalized by Anne Baanen in
`Mathlib.RingTheory.Trace.Defs`. The dual tensor–Hom and contraction
formalization by Oliver Nash and Antoine Labelle in
`Mathlib.LinearAlgebra.Contraction` supplies the rank-one trace approach used
in `ProjectiveModules.Module.Trace.Basic` and the cyclicity approach in
`ProjectiveModules.Module.Trace.Cyclicity`. Projectivity in a scalar tower is
provided by `ProjectiveModules.Module.ScalarRestriction` at semiring level.
-/

@[expose] public section

universe uR uA uM uT

namespace LinearMap

/-- The trace of an `A`-linear endomorphism restricted to `R` is the `R`-trace
of multiplication on `A` by its `A`-trace, when `A/R` and `M/A` are finite
projective over commutative semirings. -/
theorem traceOfFiniteProjective_restrictScalars
    (R : Type uR) (A : Type uA) (M : Type uM)
    [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M]
    [IsScalarTower R A M]
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite A M] [Module.Projective A M]
    (f : M →ₗ[A] M) :
    @traceOfFiniteProjective R _ M _ _
        (Module.Finite.trans (R := R) A M)
        (Module.Projective.trans (R := R) (S := A) (M := M))
        (f.restrictScalars R) =
      traceOfFiniteProjective R A
        (Algebra.lmul R A (traceOfFiniteProjective A M f)) := by
  let : Module.Finite R M := Module.Finite.trans (R := R) A M
  let : Module.Projective R M := Module.Projective.trans (R := R) (S := A) (M := M)
  obtain ⟨t, rfl⟩ := (dualTensorHom_bijective (R := A) (M := M) (N := M)).2 f
  induction t using TensorProduct.inductionOn with
  | tmul φ m =>
      have h₁ : (dualTensorHom A M M (TensorProduct.tmul A φ m)).restrictScalars R =
          ((LinearMap.toSpanSingleton A M m).restrictScalars R).comp
            (φ.restrictScalars R) := by
        apply LinearMap.ext
        intro x
        exact dualTensorHom_apply φ x m
      have h₂ : (φ.restrictScalars R).comp
          ((LinearMap.toSpanSingleton A M m).restrictScalars R) =
          Algebra.lmul R A (φ m) := by
        apply LinearMap.ext
        intro a
        change φ (a • m) = (Algebra.lmul R A (φ m)) a
        simp only [Algebra.coe_lmul_eq_mul, mul_apply', map_smul, smul_eq_mul, mul_comm]
      rw [h₁, traceOfFiniteProjective_comp_comm R M A, h₂,
        traceOfFiniteProjective_dualTensorHom, contractLeft_apply]
  | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, restrictScalars_add, h₁, h₂]

/-- On a finite free tower of commutative rings, the restriction-of-scalars
identity for multiplication by `x` is equivalent to the symmetry of the
algebra-element trace identity `Algebra.trace_trace`. -/
theorem traceOfFiniteProjective_restrictScalars_lmul_iff_trace_trace
    (R : Type uR) (A : Type uA) (T : Type uT)
    [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra A T] [Algebra R T] [IsScalarTower R A T]
    [Module.Free R A] [Module.Finite R A]
    [Module.Free A T] [Module.Finite A T]
    (x : T) :
    (@traceOfFiniteProjective R _ T _ _
        (Module.Finite.trans (R := R) A T)
        (Module.Projective.trans (R := R) (S := A) (M := T))
        ((Algebra.lmul A T x).restrictScalars R) =
      traceOfFiniteProjective R A
        (Algebra.lmul R A (traceOfFiniteProjective A T (Algebra.lmul A T x)))) ↔
      (Algebra.trace R T x = Algebra.trace R A (Algebra.trace A T x)) := by
  let : Module.Free R T := Module.Free.trans (R := R) (S := A) (M := T)
  let : Module.Finite R T := Module.Finite.trans (R := R) A T
  have hlmul : (Algebra.lmul A T x).restrictScalars R = Algebra.lmul R T x := by
    ext y
    rfl
  rw [traceOfFiniteProjective_eq_trace R T, traceOfFiniteProjective_eq_trace R A,
    traceOfFiniteProjective_eq_trace A T, hlmul]
  simp only [Algebra.trace_apply]

end LinearMap
