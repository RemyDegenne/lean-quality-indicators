/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# Duals of finite projective modules and base change

This file proves that taking the dual of a finite projective module commutes
with arbitrary scalar extension. It generalizes `IsBaseChange.dual`, whose
mathlib statement assumes that the original module is finite free.
-/

@[expose] public section

open TensorProduct

namespace IsBaseChange

open Module LinearEquiv

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  {A : Type*} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W]
  {j : V →ₗ[R] W} (ibc : IsBaseChange A j)

set_option backward.privateInPublic true in
private noncomputable def toDualBaseChangeOfProjectiveAux :
    A ⊗[R] Dual R V →ₗ[A] Dual A W where
  toAddHom := (TensorProduct.lift {
    toFun a := a • ibc.toDual
    map_add' a b := by simp [add_smul]
    map_smul' r a := by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.inductionOn with
    | add x y hx hy => aesop
    | tmul b f => simp [TensorProduct.smul_tmul', mul_smul]

set_option backward.privateInPublic true in
private theorem toDualBaseChangeOfProjectiveAux_tmul
    (a : A) (f : Dual R V) (v : V) :
    (toDualBaseChangeOfProjectiveAux ibc (a ⊗ₜ[R] f)) (j v) =
      a * algebraMap R A (f v) := by
  simp [toDualBaseChangeOfProjectiveAux, toDual_comp_apply]

variable [Module.Finite R V] [Projective R V]

set_option backward.privateInPublic true in
private noncomputable def toDualBaseChangeOfProjectiveComparison :
    A ⊗[R] Dual R V ≃ₗ[R] Dual A W :=
  (TensorProduct.comm R A (Dual R V)).trans
    ((dualTensorHomEquiv R V A).trans
      ((LinearMap.liftBaseChangeEquiv A).restrictScalars R |>.trans
        ((LinearEquiv.congrLeft A A ibc.equiv).restrictScalars R)))

set_option backward.privateInPublic true in
private theorem toDualBaseChangeOfProjectiveAux_bijective :
    Function.Bijective (toDualBaseChangeOfProjectiveAux ibc) := by
  suffices (toDualBaseChangeOfProjectiveAux ibc : A ⊗[R] Dual R V → Dual A W) =
      toDualBaseChangeOfProjectiveComparison ibc by
    exact this.symm ▸ (toDualBaseChangeOfProjectiveComparison ibc).bijective
  funext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a f =>
    apply LinearMap.ext
    intro w
    induction w using ibc.inductionOn with
    | tmul v =>
      simp [toDualBaseChangeOfProjectiveAux_tmul,
        toDualBaseChangeOfProjectiveComparison, LinearEquiv.congrLeft,
        Algebra.smul_def, mul_comm]
    | smul a w h => simp [h]
    | add x y hx hy => simp [hx, hy]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- For a finite projective module, the canonical scalar extension of its dual
is linearly equivalent to the dual of any supplied scalar extension. -/
noncomputable def toDualBaseChangeOfProjective :
    A ⊗[R] Dual R V ≃ₗ[A] Dual A W :=
  LinearEquiv.ofBijective (toDualBaseChangeOfProjectiveAux ibc)
    (toDualBaseChangeOfProjectiveAux_bijective ibc)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp] theorem toDualBaseChangeOfProjective_tmul
    (a : A) (f : Dual R V) (v : V) :
    (toDualBaseChangeOfProjective ibc (a ⊗ₜ[R] f)) (j v) =
      a * algebraMap R A (f v) :=
  toDualBaseChangeOfProjectiveAux_tmul ibc a f v

@[simp] theorem toDualBaseChangeOfProjective_one_tmul (f : Dual R V) :
    toDualBaseChangeOfProjective ibc (1 ⊗ₜ[R] f) = ibc.toDual f := by
  apply LinearMap.ext
  intro w
  induction w using ibc.inductionOn with
  | tmul v => simp [toDual_comp_apply]
  | smul a w h => simp [h]
  | add x y hx hy => simp [hx, hy]

/-- Taking the dual of a finite projective module commutes with arbitrary
scalar extension. -/
theorem dual_of_projective : IsBaseChange A ibc.toDual := by
  apply of_equiv (toDualBaseChangeOfProjective ibc)
  intro f
  simp [toDualBaseChangeOfProjective, toDualBaseChangeOfProjectiveAux]

end IsBaseChange
