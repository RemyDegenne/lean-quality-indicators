/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tensor products of projective module classes

For a commutative ring `R`, `KTheory.ProjectiveClass.tensorMul` sends the classes
of finite projective right modules `M` and `N` to the class of
`M ⊗[Rᵐᵒᵖ] N`. The original right-module structures supply the canonical tensor
module structure. The ring may be the zero ring, and the module carriers may
inhabit independent universes.

Tensor multiplication makes `ProjectiveClass R` a commutative semiring, with
the regular right-module class `of R Rᵐᵒᵖ` as its unit and direct sum as addition.
Its natural-number casts are direct sums of the regular class. The characteristic
lemmas `mul_eq_tensorMul`, `one_eq_of` and `natCast_eq_nsmul` relate semiring
arithmetic to the module-class API; `of_prod` characterizes addition.
These constructions hold for every commutative ring, including the zero ring.

## Implementation notes

The construction descends an isomorphism-invariant function in each argument
and retains the entire direct-sum additive monoid, including its stored
natural-number scaling. A left `Rᵐᵒᵖ`-module represents a genuine right `R`-module;
for the scalar-self module `Rᵐᵒᵖ`, the action is
`(op r) • (op x) = op (x * r)`. The additive Grothendieck group `K0 R` and
its canonical additive map are unchanged; no multiplication on `K0 R` is defined here.

## References and credits

The tensor-product operation on projective classes appears in Charles A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2.
The zero-ring case extends Weibel's standing nonzero-ring convention.
This construction uses this library's finite-projective representatives and
isomorphism-invariant function descent, together with Mathlib's tensor
congruence, associativity, symmetry, unit equivalences, product equivalences,
and finite-generation and projectivity instances for tensor products.
-/

@[expose] public section

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace KTheory.ProjectiveClass

variable (R : Type u) [CommRing R]

private theorem tensorClass_congr_right
    (X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ)
    {Y Y' : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ} (e : Y ≅ Y') :
    of R (X ⊗[Rᵐᵒᵖ] Y) = of R (X ⊗[Rᵐᵒᵖ] Y') :=
  of_eq_of_equiv R _
    (TensorProduct.congr (LinearEquiv.refl Rᵐᵒᵖ X)
      (ModuleCat.FiniteProjective.isoToLinearEquiv e))

private noncomputable def tensorMulAux
    (X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    ProjectiveClass R → ProjectiveClass R :=
  liftFunction R
    (fun Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ ↦ of R (X ⊗[Rᵐᵒᵖ] Y))
    (tensorClass_congr_right R X)

private theorem tensorMulAux_of
    (X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    tensorMulAux R X (of R Y) = of R (X ⊗[Rᵐᵒᵖ] Y) := by
  exact liftFunction_of R
    (fun Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ ↦ of R (X ⊗[Rᵐᵒᵖ] Y))
    (tensorClass_congr_right R X) Y

private theorem tensorMulAux_congr
    {X X' : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ} (e : X ≅ X') :
    tensorMulAux R X = tensorMulAux R X' := by
  funext b
  exact induction_on R b (fun Y ↦ by
    rw [tensorMulAux_of, tensorMulAux_of]
    exact of_eq_of_equiv R _
      (TensorProduct.congr (ModuleCat.FiniteProjective.isoToLinearEquiv e)
        (LinearEquiv.refl Rᵐᵒᵖ Y)))

/-- Tensor product of finite projective right-module classes over a commutative
ring, with tensor product taken over the opposite scalar ring. -/
@[no_expose]
noncomputable def tensorMul : ProjectiveClass R → ProjectiveClass R → ProjectiveClass R :=
  liftFunction R (tensorMulAux R) (tensorMulAux_congr R)

/-- On reference-module classes, tensor multiplication evaluates to the class
of the tensor product. -/
theorem tensorMul_of (X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    tensorMul R (of R X) (of R Y) = of R (X ⊗[Rᵐᵒᵖ] Y) := by
  calc
    tensorMul R (of R X) (of R Y) = tensorMulAux R X (of R Y) :=
      congrFun (liftFunction_of R (tensorMulAux R) (tensorMulAux_congr R) X) (of R Y)
    _ = of R (X ⊗[Rᵐᵒᵖ] Y) := tensorMulAux_of R X Y

/-- Tensor multiplication computes the class of the tensor product for finite
projective right modules in independent carrier universes. -/
@[simp]
theorem tensorMul_of_module
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    tensorMul R (of R M) (of R N) = of R (M ⊗[Rᵐᵒᵖ] N) := by
  rw [← of_repr R M, ← of_repr R N, tensorMul_of]
  exact of_eq_of_equiv R _
    (TensorProduct.congr (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ M)
      (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ N))

/-- Tensor multiplication of projective classes is associative, as in the tensor
semiring of Weibel's *The K-book*, Chapter II, §2. -/
theorem tensorMul_assoc (a b c : ProjectiveClass R) :
    tensorMul R (tensorMul R a b) c = tensorMul R a (tensorMul R b c) := by
  refine induction_on R a ?_
  intro M
  refine induction_on R b ?_
  intro N
  refine induction_on R c ?_
  intro P
  simpa only [tensorMul_of_module] using
    (of_eq_of_equiv R ((M ⊗[Rᵐᵒᵖ] N) ⊗[Rᵐᵒᵖ] P)
      (TensorProduct.assoc Rᵐᵒᵖ M N P))

/-- Tensor multiplication of projective classes is commutative, as in the tensor
semiring of Weibel's *The K-book*, Chapter II, §2. -/
theorem tensorMul_comm (a b : ProjectiveClass R) :
    tensorMul R a b = tensorMul R b a := by
  refine induction_on R a ?_
  intro M
  refine induction_on R b ?_
  intro N
  simpa only [tensorMul_of_module] using
    (of_eq_of_equiv R (M ⊗[Rᵐᵒᵖ] N) (TensorProduct.comm Rᵐᵒᵖ M N))

/-- The regular right-module class is a left unit for tensor multiplication,
as in Weibel's *The K-book*, Chapter II, §2. -/
@[simp]
theorem regular_tensorMul (a : ProjectiveClass R) :
    tensorMul R (of R Rᵐᵒᵖ) a = a := by
  refine induction_on R a ?_
  intro M
  simpa only [tensorMul_of_module] using
    (of_eq_of_equiv R (Rᵐᵒᵖ ⊗[Rᵐᵒᵖ] M) (TensorProduct.lid Rᵐᵒᵖ M))

/-- The regular right-module class is a right unit for tensor multiplication,
as in Weibel's *The K-book*, Chapter II, §2. -/
@[simp]
theorem tensorMul_regular (a : ProjectiveClass R) :
    tensorMul R a (of R Rᵐᵒᵖ) = a := by
  refine induction_on R a ?_
  intro M
  simpa only [tensorMul_of_module] using
    (of_eq_of_equiv R (M ⊗[Rᵐᵒᵖ] Rᵐᵒᵖ) (TensorProduct.rid Rᵐᵒᵖ M))

/-- Tensor multiplication distributes over direct sum in its second argument,
as in the tensor semiring of Weibel's *The K-book*, Chapter II, §2. -/
theorem tensorMul_add (a b c : ProjectiveClass R) :
    tensorMul R a (b + c) = tensorMul R a b + tensorMul R a c := by
  refine induction_on R a fun X ↦ ?_
  refine induction_on R b fun Y ↦ ?_
  refine induction_on R c fun Z ↦ ?_
  rw [← of_prod R Y Z, tensorMul_of_module, tensorMul_of_module,
    tensorMul_of_module, ← of_prod]
  exact of_eq_of_equiv R _
    (TensorProduct.prodRight Rᵐᵒᵖ Rᵐᵒᵖ X Y Z)

/-- Tensor multiplication distributes over direct sum in its first argument,
as in the tensor semiring of Weibel's *The K-book*, Chapter II, §2. -/
theorem add_tensorMul (a b c : ProjectiveClass R) :
    tensorMul R (a + b) c = tensorMul R a c + tensorMul R b c := by
  refine induction_on R a fun X ↦ ?_
  refine induction_on R b fun Y ↦ ?_
  refine induction_on R c fun Z ↦ ?_
  rw [← of_prod R X Y, tensorMul_of_module, tensorMul_of_module,
    tensorMul_of_module, ← of_prod]
  exact of_eq_of_equiv R _
    (TensorProduct.prodLeft Rᵐᵒᵖ Rᵐᵒᵖ X Y Z)

/-- Tensoring the zero class with any class gives the zero class, as in the tensor
semiring of Weibel's *The K-book*, Chapter II, §2. -/
@[simp]
theorem zero_tensorMul (a : ProjectiveClass R) : tensorMul R 0 a = 0 := by
  refine induction_on R a fun X ↦ ?_
  simpa only [of_zero] using (tensorMul_of_module R PUnit.{u + 1} X)

/-- Tensoring any class with the zero class gives the zero class, as in the tensor
semiring of Weibel's *The K-book*, Chapter II, §2. -/
@[simp]
theorem tensorMul_zero (a : ProjectiveClass R) : tensorMul R a 0 = 0 := by
  refine induction_on R a fun X ↦ ?_
  simpa only [of_zero] using (tensorMul_of_module R X PUnit.{u + 1})

private noncomputable abbrev directSumAddCommMonoid : AddCommMonoid (ProjectiveClass R) :=
  inferInstance

private noncomputable abbrev k0AddCommGroup : AddCommGroup (K0 R) :=
  inferInstance

private noncomputable abbrev completionMap : ProjectiveClass R →+ K0 R :=
  K0.ofClass R

/-- The tensor semiring of finite projective right-module classes over a commutative ring,
with direct-sum addition and the regular right-module class as unit, as in Weibel's
*The K-book*, Chapter II, §2. The zero ring is allowed. Natural-number casts use the
stored scaling of the direct-sum additive monoid. -/
noncomputable instance instCommSemiring : CommSemiring (ProjectiveClass R) where
  __ := KTheory.instAddCommMonoidProjectiveClass R
  mul := tensorMul R
  one := of R Rᵐᵒᵖ
  mul_assoc := tensorMul_assoc R
  mul_comm := tensorMul_comm R
  one_mul := regular_tensorMul R
  mul_one := tensorMul_regular R
  left_distrib := tensorMul_add R
  right_distrib := add_tensorMul R
  zero_mul := zero_tensorMul R
  mul_zero := tensorMul_zero R
  natCast n := (KTheory.instAddCommMonoidProjectiveClass R).nsmul n (of R Rᵐᵒᵖ)
  natCast_zero := (KTheory.instAddCommMonoidProjectiveClass R).nsmul_zero (of R Rᵐᵒᵖ)
  natCast_succ n := (KTheory.instAddCommMonoidProjectiveClass R).nsmul_succ n (of R Rᵐᵒᵖ)

private theorem instCommSemiring_toAddCommMonoid :
    (instCommSemiring R).toAddCommMonoid = directSumAddCommMonoid R := rfl

private theorem directSumAddCommMonoid_eq :
    (inferInstance : AddCommMonoid (ProjectiveClass R)) = directSumAddCommMonoid R := rfl

private theorem k0AddCommGroup_eq :
    (inferInstance : AddCommGroup (K0 R)) = k0AddCommGroup R := rfl

private theorem completionMap_eq :
    (K0.ofClass R : ProjectiveClass R →+ K0 R) = completionMap R := rfl

/-- Multiplication of projective classes is their tensor product. -/
theorem mul_eq_tensorMul (a b : ProjectiveClass R) :
    a * b = tensorMul R a b := rfl

/-- Multiplication of module classes computes the tensor-product class, with
independent carrier universes for the two finite projective right modules. -/
@[simp]
theorem of_mul
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    of R M * of R N = of R (M ⊗[Rᵐᵒᵖ] N) := by
  rw [mul_eq_tensorMul, tensorMul_of_module]

/-- The semiring unit is the regular right-module class. -/
theorem one_eq_of : (1 : ProjectiveClass R) = of R Rᵐᵒᵖ := rfl

/-- Natural-number casts are direct sums of the regular right-module class. -/
theorem natCast_eq_nsmul (n : ℕ) :
    (n : ProjectiveClass R) = n • of R Rᵐᵒᵖ := rfl

end KTheory.ProjectiveClass
