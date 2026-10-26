/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Finite projective modules over Laurent polynomial rings

The one-variable Laurent polynomial ring over a field is a principal ideal
ring.  Consequently, every finitely generated projective module over it is
free.  The final theorem gives the literal opposite-ring formulation for right
modules.
-/

@[expose] public section

open scoped LaurentPolynomial nonZeroDivisors Polynomial

noncomputable section

universe uF uP

namespace LaurentPolynomial

/-- The one-variable Laurent polynomial ring over a field is a principal ideal
ring. -/
instance instIsPrincipalIdealRingOfField (F : Type uF) [Field F] :
    IsPrincipalIdealRing F[T;T⁻¹] := by
  let _ : IsDedekindDomain F[X] := inferInstance
  let _ : IsDedekindDomain F[T;T⁻¹] :=
    IsLocalization.isDedekindDomain F[X]
      (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero) F[T;T⁻¹]
  let _ : UniqueFactorizationMonoid F[T;T⁻¹] :=
    UniqueFactorizationMonoid.of_isLocalization
      (Submonoid.powers (Polynomial.X : F[X])) F[T;T⁻¹]
  exact IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid F[T;T⁻¹]

/-- The opposite of a one-variable Laurent polynomial ring over a field is a
principal ideal ring.  This is the scalar ring for literal right modules. -/
instance instIsPrincipalIdealRingOppositeOfField (F : Type uF) [Field F] :
    IsPrincipalIdealRing F[T;T⁻¹]ᵐᵒᵖ :=
  IsPrincipalIdealRing.of_surjective (RingEquiv.toOpposite F[T;T⁻¹]).toRingHom
    (RingEquiv.toOpposite F[T;T⁻¹]).surjective

/-- A finitely generated projective module over the one-variable Laurent
polynomial ring over a field is free. -/
theorem module_free_of_finite_projective
    (F : Type uF) (P : Type uP) [Field F] [AddCommGroup P]
    [Module F[T;T⁻¹] P] [Module.Finite F[T;T⁻¹] P]
    [Module.Projective F[T;T⁻¹] P] : Module.Free F[T;T⁻¹] P := by
  let _ : Module.Flat F[T;T⁻¹] P := Module.Flat.of_projective
  let _ : Module.IsTorsionFree F[T;T⁻¹] P := Module.Flat.isTorsionFree
  exact Module.free_of_finite_type_torsion_free'

/-- A finitely generated projective right module over the one-variable Laurent
polynomial ring over a field is free, with the right action represented as a
left action of the opposite ring. -/
theorem op_module_free_of_finite_projective
    (F : Type uF) (P : Type uP) [Field F] [AddCommGroup P]
    [Module F[T;T⁻¹]ᵐᵒᵖ P] [Module.Finite F[T;T⁻¹]ᵐᵒᵖ P]
    [Module.Projective F[T;T⁻¹]ᵐᵒᵖ P] : Module.Free F[T;T⁻¹]ᵐᵒᵖ P := by
  let _ : Module.Flat F[T;T⁻¹]ᵐᵒᵖ P := Module.Flat.of_projective
  let _ : Module.IsTorsionFree F[T;T⁻¹]ᵐᵒᵖ P := Module.Flat.isTorsionFree
  exact Module.free_of_finite_type_torsion_free'

end LaurentPolynomial
