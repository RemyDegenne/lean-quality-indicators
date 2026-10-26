/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.TensorProduct.Finite
public import ProjectiveModules.Module.ProjectiveComplement

/-!
# Stable cancellation for invertible modules

This file proves that a common finite free summand can be cancelled from two
invertible modules. The proof tensors a stabilization by the dual of the second
module, constructs a finite free complement to the resulting finite projective
summand, and applies the theorem that an invertible stably free module is free.
-/

@[expose] public section

open scoped TensorProduct

namespace Module

universe u v w

variable {R : Type u} [CommRing R]

namespace Invertible

variable {L : Type v} {L' : Type w}
variable [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
variable [Module.Invertible R L] [Module.Invertible R L']

/-- Tensoring a finite-free stabilization by the dual of `L'` reduces it to a
stabilization of `L ⊗ (L')ᵛ` by the same finite projective module. -/
noncomputable def tensorFinStabilization (n : ℕ)
    (e : (L × (Fin n → R)) ≃ₗ[R] (L' × (Fin n → R))) :
    ((L ⊗[R] Module.Dual R L') × ((Fin n → R) ⊗[R] Module.Dual R L')) ≃ₗ[R]
      (R × ((Fin n → R) ⊗[R] Module.Dual R L')) :=
  (TensorProduct.prodLeft R R L (Fin n → R) (Module.Dual R L')).symm ≪≫ₗ
    LinearEquiv.rTensor (M := Module.Dual R L') e ≪≫ₗ
    TensorProduct.prodLeft R R L' (Fin n → R) (Module.Dual R L') ≪≫ₗ
    ((TensorProduct.comm R L' (Module.Dual R L') ≪≫ₗ
      Module.Invertible.linearEquiv R L').prodCongr
        (LinearEquiv.refl R ((Fin n → R) ⊗[R] Module.Dual R L')))

/-- A common finite free summand can be cancelled from two invertible modules. -/
theorem nonempty_linearEquiv_of_fin_stabilization (n : ℕ)
    (e : (L × (Fin n → R)) ≃ₗ[R] (L' × (Fin n → R))) :
    Nonempty (L ≃ₗ[R] L') := by
  let A := L ⊗[R] Module.Dual R L'
  let B := (Fin n → R) ⊗[R] Module.Dual R L'
  let eAB : (A × B) ≃ₗ[R] (R × B) := tensorFinStabilization n e
  have hBFinite : Module.Finite R B := inferInstance
  have hBProjective : Module.Projective R B := inferInstance
  let _ : Module.Finite R B := hBFinite
  let _ : Module.Projective R B := hBProjective
  obtain ⟨C, hCgroup, hCmodule, hCfinite, hBCfinite, hBCfree⟩ :=
    Module.exists_finite_free_product_of_finite_projective (R := R) (B := B)
  let _ : AddCommGroup C := hCgroup
  let _ : Module R C := hCmodule
  let _ : Module.Finite R C := hCfinite
  let _ : Module.Finite R (B × C) := hBCfinite
  let _ : Module.Free R (B × C) := hBCfree
  have hAprodFree : Module.Free R (A × (B × C)) := by
    have htarget : Module.Free R (R × (B × C)) := inferInstance
    let q : (A × (B × C)) ≃ₗ[R] (R × (B × C)) :=
      (LinearEquiv.prodAssoc R A B C).symm ≪≫ₗ
        LinearEquiv.prodCongr eAB (LinearEquiv.refl R C) ≪≫ₗ
        LinearEquiv.prodAssoc R R B C
    exact Module.Free.of_equiv' htarget q.symm
  let _ : Module.Free R (A × (B × C)) := hAprodFree
  let _ : Module.IsStablyFree R A := Module.IsStablyFree.of_free_prod R A (B × C)
  have hAFree : Module.Free R A := Module.free_of_isStablyFree_of_invertible R A
  have hpicA : CommRing.Pic.mk R A = 1 :=
    CommRing.Pic.mk_eq_one_iff_free.mpr hAFree
  have hpic : CommRing.Pic.mk R L = CommRing.Pic.mk R L' := by
    rw [CommRing.Pic.mk_tensor, CommRing.Pic.mk_dual] at hpicA
    exact mul_inv_eq_one.mp (by simpa using hpicA)
  exact CommRing.Pic.mk_eq_mk_iff.mp hpic

end Invertible

end Module
