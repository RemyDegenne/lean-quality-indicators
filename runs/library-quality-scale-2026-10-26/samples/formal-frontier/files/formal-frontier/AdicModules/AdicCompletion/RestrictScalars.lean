/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps

set_option warningAsError true

/-!
# Adic completion and restriction of scalars

Let `R → S` be an algebra, `M` an `S`-module with a compatible `R`-module structure,
and `I` an ideal of `R`. The filtration of `M` by the powers of `I` agrees, after
restriction of scalars, with the filtration by powers of the extended ideal in `S`.
Thus their native quotients and their inverse-limit adic completions are linearly
equivalent over `R`. No finiteness, separatedness, or completeness assumption is used.

The equivalence goes from completion along the extended ideal to completion
along `I`. Its inverse, both quotient representatives, and the native transition
maps are described by the accompanying lemmas.

## References

The comparison uses Mathlib's ideal-map/power identity,
`Submodule.Quotient.restrictScalarsEquiv`, representative-preserving
`Submodule.quotEquivOfEq` and compatible-family `AdicCompletion` interfaces.
The original project implementation and its distinct library adaptation are
credited in `docs/CREDITS.md`.
-/

@[expose] public section

namespace AdicCompletion

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The powers of an extended ideal act on `M` by the same submodules after
restriction of scalars as the corresponding powers of the original ideal. -/
theorem map_pow_smul_top_restrictScalars (I : Ideal R) (n : ℕ) :
    (((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)).restrictScalars R) =
      I ^ n • (⊤ : Submodule R M) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq]
  rfl

/-- The level-`n` quotient comparison, from the extended-ideal quotient to the
original-ideal quotient, linear over `R`. -/
def restrictScalarsLevelEquiv (I : Ideal R) (N : Type*) [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] (n : ℕ) :
    (N ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S N)) ≃ₗ[R]
      N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  (Submodule.Quotient.restrictScalarsEquiv R
      ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S N))).symm.trans
    (Submodule.quotEquivOfEq _ _ (map_pow_smul_top_restrictScalars (M := N) I n))

@[simp]
theorem restrictScalarsLevelEquiv_mk (I : Ideal R) (n : ℕ) (x : M) :
    restrictScalarsLevelEquiv I M n
      (Submodule.Quotient.mk x :
        M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) =
      (Submodule.Quotient.mk x : M ⧸ (I ^ n • ⊤ : Submodule R M)) := by
  simp [restrictScalarsLevelEquiv]

@[simp]
theorem restrictScalarsLevelEquiv_symm_mk (I : Ideal R) (n : ℕ) (x : M) :
    (restrictScalarsLevelEquiv I M n).symm
      (Submodule.Quotient.mk x : M ⧸ (I ^ n • ⊤ : Submodule R M)) =
      (Submodule.Quotient.mk x :
        M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) := by
  apply (restrictScalarsLevelEquiv I M n).injective
  simp

/-- The level comparisons commute with the native transition maps. -/
theorem restrictScalarsLevelEquiv_transitionMap (I : Ideal R) {m n : ℕ}
    (hmn : m ≤ n)
    (x : M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) :
    restrictScalarsLevelEquiv I M m
        (transitionMap (I.map (algebraMap R S)) M hmn x) =
      transitionMap I M hmn (restrictScalarsLevelEquiv I M n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change restrictScalarsLevelEquiv I M m
      (Submodule.factor _ (Submodule.mkQ _ x)) =
        Submodule.factor _ (restrictScalarsLevelEquiv I M n (Submodule.mkQ _ x))
    simp

/-- The inverse level comparisons commute with the native transition maps. -/
theorem restrictScalarsLevelEquiv_symm_transitionMap (I : Ideal R) {m n : ℕ}
    (hmn : m ≤ n) (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    (restrictScalarsLevelEquiv I M m).symm (transitionMap I M hmn x) =
      transitionMap (I.map (algebraMap R S)) M hmn
        ((restrictScalarsLevelEquiv I M n).symm x) := by
  apply (restrictScalarsLevelEquiv I M m).injective
  rw [restrictScalarsLevelEquiv_transitionMap]
  simp

/-- Restricting scalars commutes with forming the native inverse-limit
completion: extended-ideal completion is the original-ideal completion as an
`R`-module. -/
def restrictScalarsEquiv (I : Ideal R) (N : Type*) [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] :
    AdicCompletion (I.map (algebraMap R S)) N ≃ₗ[R] AdicCompletion I N where
  toFun x := ⟨fun n => restrictScalarsLevelEquiv I N n (x.val n), by
    intro m n hmn
    rw [← restrictScalarsLevelEquiv_transitionMap I hmn]
    exact congrArg (restrictScalarsLevelEquiv I N m) (x.property hmn)⟩
  invFun x := ⟨fun n => (restrictScalarsLevelEquiv I N n).symm (x.val n), by
    intro m n hmn
    change transitionMap (I.map (algebraMap R S)) N hmn
        ((restrictScalarsLevelEquiv I N n).symm (x.val n)) =
      (restrictScalarsLevelEquiv I N m).symm (x.val m)
    rw [← restrictScalarsLevelEquiv_symm_transitionMap I hmn]
    exact congrArg (restrictScalarsLevelEquiv I N m).symm (x.property hmn)⟩
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (restrictScalarsLevelEquiv I N n).symm_apply_apply (x.val n)
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (restrictScalarsLevelEquiv I N n).apply_symm_apply (x.val n)
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact (restrictScalarsLevelEquiv I N n).map_add (x.val n) (y.val n)
  map_smul' a x := by
    apply AdicCompletion.ext
    intro n
    exact (restrictScalarsLevelEquiv I N n).map_smul a (x.val n)

@[simp]
theorem restrictScalarsEquiv_eval (I : Ideal R)
    (x : AdicCompletion (I.map (algebraMap R S)) M) (n : ℕ) :
    eval I M n (restrictScalarsEquiv I M x) =
      restrictScalarsLevelEquiv I M n
        (eval (I.map (algebraMap R S)) M n x) :=
  rfl

@[simp]
theorem restrictScalarsEquiv_symm_eval (I : Ideal R) (x : AdicCompletion I M) (n : ℕ) :
    eval (I.map (algebraMap R S)) M n ((restrictScalarsEquiv I M).symm x) =
      (restrictScalarsLevelEquiv I M n).symm (eval I M n x) :=
  rfl

@[simp]
theorem restrictScalarsEquiv_of (I : Ideal R) (x : M) :
    restrictScalarsEquiv I M (of (I.map (algebraMap R S)) M x) = of I M x := by
  apply AdicCompletion.ext
  intro n
  exact restrictScalarsLevelEquiv_mk I n x

@[simp]
theorem restrictScalarsEquiv_symm_of (I : Ideal R) (x : M) :
    (restrictScalarsEquiv I M).symm (of I M x) =
      of (I.map (algebraMap R S)) M x := by
  apply (restrictScalarsEquiv I M).injective
  simp

end AdicCompletion
