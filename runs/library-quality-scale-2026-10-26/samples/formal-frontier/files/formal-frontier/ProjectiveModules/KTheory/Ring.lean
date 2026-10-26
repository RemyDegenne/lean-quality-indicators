/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.TensorProduct
public import GroupTheory.MonoidLocalization.GrothendieckGroup.Ring

/-!
# The tensor-product ring on K₀

For every commutative ring `R`, tensor product makes `KTheory.K0 R` a commutative
ring. The unit is the class of the regular right module, and multiplication of
module generators is the generator of their tensor product over `Rᵐᵒᵖ`. The zero
ring is allowed, and the two module carriers may inhabit independent universes.

`KTheory.K0.ofClassRingHom` bundles the map from the tensor semiring of projective
classes to K₀. Its entire underlying additive map is `KTheory.K0.ofClass`.
Addition remains direct sum, and natural and integer casts are the corresponding
multiples of the regular right-module generator.

## Universal property

The ring instance is supplied by
`Algebra.GrothendieckAddGroup.instCommRing` on `ProjectiveClass R`.
The carrier is the additive Grothendieck group from `KTheory.K0`, with the same
additive group and stored operations. The generic APIs apply directly:

* `Algebra.GrothendieckAddGroup.liftRingHom` extends any ring homomorphism
  `ProjectiveClass R →+* S` to `K0 R →+* S`.
* `Algebra.GrothendieckAddGroup.liftRingHom_of` evaluates this extension on class
  generators; `liftRingHom_toAddMonoidHom` identifies its whole additive lift.
* `Algebra.GrothendieckAddGroup.ringHom_ext` gives extensionality on class
  generators, and `liftRingEquiv` packages extension and restriction as inverse maps.

Here `S` is any ring in an independent universe: neither commutativity nor
nontriviality is required. These APIs need no separate K₀ lifting construction.

## References and credits

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II, §2, the tensor-product ring on K₀. The zero-ring case extends
  the book's nonzero-ring convention.
* This library's finite-projective class, tensor-semiring and K₀ formalizations.
* Formal Frontier's Group Theory ring structure, generator and universal property
  for additive Grothendieck groups.
* Alex J. Best and Yaël Dillies' Mathlib Grothendieck completion and its additive
  universal property, and Mathlib's tensor-product formalization.
-/

@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace KTheory.K0

variable (R : Type uR) [CommRing R]

/-- The ring homomorphism from the tensor semiring of finite projective
right-module classes to K₀. Its additive map is the completion map. -/
noncomputable def ofClassRingHom : ProjectiveClass R →+* K0 R :=
  Algebra.GrothendieckAddGroup.ofRingHom (ProjectiveClass R)

/-- Forgetting multiplication retains the entire additive completion map. -/
@[simp]
theorem ofClassRingHom_toAddMonoidHom :
    (ofClassRingHom R).toAddMonoidHom = ofClass R := rfl

/-- The ring homomorphism evaluates as the additive completion map. -/
@[simp]
theorem ofClassRingHom_apply (a : ProjectiveClass R) :
    ofClassRingHom R a = ofClass R a := rfl

/-- A finite projective right-module class maps to its K₀ generator,
independently of the module's carrier universe. -/
theorem ofClassRingHom_of
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    ofClassRingHom R (ProjectiveClass.of R M) = of R M := rfl

/-- The ring unit is the K₀ generator of the regular right module. -/
theorem one_eq_of : (1 : K0 R) = of R Rᵐᵒᵖ := rfl

/-- The regular right-module generator is the ring unit. -/
@[simp]
theorem of_self : of R Rᵐᵒᵖ = 1 := rfl

/-- Multiplication of finite projective right-module generators computes their
tensor product, with independent carrier universes for the two modules. -/
@[simp]
theorem of_mul
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (N : Type uN) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    of R M * of R N = of R (M ⊗[Rᵐᵒᵖ] N) := by
  calc
    of R M * of R N =
        ofClassRingHom R (ProjectiveClass.of R M * ProjectiveClass.of R N) :=
      ((ofClassRingHom R).map_mul _ _).symm
    _ = of R (M ⊗[Rᵐᵒᵖ] N) := by
      rw [ProjectiveClass.of_mul, ofClassRingHom_of]

/-- Natural-number casts are natural multiples of the regular right-module generator. -/
theorem natCast_eq_nsmul (n : ℕ) : (n : K0 R) = n • of R Rᵐᵒᵖ := rfl

/-- Integer casts are integer multiples of the regular right-module generator. -/
theorem intCast_eq_zsmul (z : ℤ) : (z : K0 R) = z • of R Rᵐᵒᵖ := rfl

end KTheory.K0
