/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.TrivSqZeroExt.Finite

/-!
# Ideal-to-module transfer over finite-type algebras

An isomorphism-invariant property of finite modules that descends through every
surjective square-zero algebra map holds for all finite modules precisely when
it holds for all finitely generated ideals. The base ring may have a different
universe from the common universe of algebra carriers and their modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open scoped TensorProduct
open scoped TrivSqZeroExt

universe uA u

namespace Ideal

variable {A : Type uA} [CommRing A]
variable (P : ∀ (B : Type u) [CommRing B] [Algebra A B],
  (N : Type u) → [AddCommGroup N] → [Module B N] → Prop)

/-- Testing an isomorphism-invariant, square-zero-descent-stable property on
finitely generated ideals suffices to test it on all finite modules over
finite-type algebras. The two directions have the same finite-type scope. -/
theorem ideal_property_iff_module_property
    (hiso : ∀ (B C : Type u) [CommRing B] [CommRing C]
      [Algebra A B] [Algebra A C]
      [Algebra.FiniteType A B] [Algebra.FiniteType A C]
      (e : B ≃ₐ[A] C) (N N' : Type u)
      [AddCommGroup N] [AddCommGroup N']
      [Module B N] [Module C N']
      [Module.Finite B N] [Module.Finite C N']
      (_ : @LinearEquiv B C _ _ e.toRingEquiv.toRingHom
        e.toRingEquiv.symm.toRingHom
        (RingHomInvPair.of_ringEquiv e.toRingEquiv)
        (RingHomInvPair.of_ringEquiv_symm e.toRingEquiv)
        N N' _ _ _ _),
      P B N ↔ P C N')
    (hdesc : ∀ (B C : Type u) [CommRing B] [CommRing C]
      [Algebra A B] [Algebra A C]
      [Algebra.FiniteType A B] [Algebra.FiniteType A C]
      [Algebra B C] [IsScalarTower A B C]
      (_hf : Function.Surjective (algebraMap B C))
      (_hsq : (RingHom.ker (algebraMap B C)) ^ 2 = ⊥)
      (N : Type u) [AddCommGroup N] [Module B N]
      [Module.Finite B N],
      P B N → P C (C ⊗[B] N)) :
    (∀ (B : Type u) [CommRing B] [Algebra A B]
      [Algebra.FiniteType A B] (I : Ideal B), I.FG → P B I) ↔
    (∀ (B : Type u) [CommRing B] [Algebra A B]
      [Algebra.FiniteType A B] (N : Type u)
      [AddCommGroup N] [Module B N] [Module.Finite B N],
      P B N) := by
  constructor
  · intro hideals B _ _ _ N _ _ _
    let : Module A N := Module.compHom N (algebraMap A B)
    let : IsScalarTower A B N := by
      constructor
      intro a b n
      change (a • b) • n = (algebraMap A B a) • (b • n)
      rw [Algebra.smul_def, mul_smul]
    let : IsScalarTower A Bᵐᵒᵖ N := by infer_instance
    let : Algebra A (TrivSqZeroExt B N) := TrivSqZeroExt.algebra' A B N
    let : IsScalarTower A B (TrivSqZeroExt B N) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : Module.Finite B (TrivSqZeroExt B N) := by
      change Module.Finite B (B × N)
      infer_instance
    have : Algebra.FiniteType B (TrivSqZeroExt B N) :=
      Module.Finite.finiteType (TrivSqZeroExt B N)
    have : Algebra.FiniteType A (TrivSqZeroExt B N) :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType A B)
        (inferInstance : Algebra.FiniteType B (TrivSqZeroExt B N))
    have : Module.Finite (TrivSqZeroExt B N) (TrivSqZeroExt.kerIdeal B N) :=
      TrivSqZeroExt.kerIdeal_finite
    have hkernel : P (TrivSqZeroExt B N) (TrivSqZeroExt.kerIdeal B N) :=
      hideals (TrivSqZeroExt B N) (TrivSqZeroExt.kerIdeal B N) Submodule.FG.of_finite
    let : Algebra (TrivSqZeroExt B N) B := TrivSqZeroExt.algebraBase B N
    let : IsScalarTower A (TrivSqZeroExt B N) B :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hbase : P B (B ⊗[TrivSqZeroExt B N] TrivSqZeroExt.kerIdeal B N) :=
      hdesc (TrivSqZeroExt B N) B
        (fun b => ⟨TrivSqZeroExt.inl b, rfl⟩)
        (TrivSqZeroExt.kerIdeal_sq B N)
        (TrivSqZeroExt.kerIdeal B N) hkernel
    exact (hiso B B (AlgEquiv.refl) _ N
      (TrivSqZeroExt.kerIdealBaseChange (R := B) (M := N))).mp hbase
  · intro hmodules B _ _ _ I hfg
    have : Module.Finite B I := Module.Finite.of_fg hfg
    exact hmodules B I

end Ideal
