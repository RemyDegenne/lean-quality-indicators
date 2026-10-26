/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite kernels and projection base change for trivial square-zero extensions

The kernel of the projection from `TrivSqZeroExt R M` is the original module `M`.
Base change along that projection recovers `M` without a finiteness assumption.
The opposite action below is the canonical action for a commutative base semiring.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open scoped TensorProduct

universe uR uM

namespace TrivSqZeroExt

variable {R : Type uR} {M : Type uM}
  [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The opposite action on a module induced by a commutative semiring action. -/
scoped instance canonicalOppositeModule : Module Rᵐᵒᵖ M :=
  Module.compHom M (RingEquiv.toOpposite R).symm.toRingHom

/-- The induced opposite action agrees with the original action. -/
scoped instance canonicalCentralScalar : IsCentralScalar R M where
  op_smul_eq_smul _ _ := rfl

/-- The projection kernel, viewed as an `R`-module, is the second coordinate. -/
noncomputable def kerIdealLinearEquiv : kerIdeal R M ≃ₗ[R] M := by
  let forward : kerIdeal R M →ₗ[R] M :=
    { toFun := fun j => j.val.snd
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let backward : M →ₗ[R] kerIdeal R M :=
    { toFun := fun m => ⟨inr m, (mem_kerIdeal_iff_inr R M (inr m)).2 (by simp)⟩
      map_add' := fun _ _ => Subtype.ext (inr_add R _ _)
      map_smul' := fun _ _ => Subtype.ext (inr_smul R _ _) }
  exact LinearEquiv.ofLinearMap forward backward
    (by
      apply LinearMap.ext
      intro m
      rfl)
    (by
      apply LinearMap.ext
      intro j
      apply Subtype.ext
      exact (mem_kerIdeal_iff_inr R M j.val).1 j.property |>.symm)

@[simp]
theorem kerIdealLinearEquiv_apply (j : kerIdeal R M) :
    kerIdealLinearEquiv (R := R) (M := M) j = j.val.snd := by
  rfl

@[simp]
theorem kerIdealLinearEquiv_symm_apply (m : M) :
    ((kerIdealLinearEquiv (R := R) (M := M)).symm m).val = inr m := by
  rfl

/-- Finite generation of `M` implies finite generation of the projection kernel over
the whole trivial square-zero extension. -/
theorem kerIdeal_finite [Module.Finite R M] :
    Module.Finite (TrivSqZeroExt R M) (kerIdeal R M) := by
  have : Module.Finite R (kerIdeal R M) :=
    Module.Finite.of_surjective (kerIdealLinearEquiv (R := R) (M := M)).symm.toLinearMap
      (kerIdealLinearEquiv (R := R) (M := M)).symm.surjective
  have : IsScalarTower R (TrivSqZeroExt R M) (kerIdeal R M) := by
    constructor
    intro r s j
    apply Subtype.ext
    change (r • s) * j.val = r • (s * j.val)
    rw [← inl_mul_eq_smul, ← inl_mul_eq_smul, mul_assoc]
  exact Module.Finite.of_restrictScalars_finite R (TrivSqZeroExt R M) (kerIdeal R M)

section ProjectionBaseChange

local instance : Algebra (TrivSqZeroExt R M) R := algebraBase R M

/-- Projection-base change of the square-zero kernel, as an `R`-linear equivalence. -/
noncomputable def kerIdealBaseChange :
    R ⊗[TrivSqZeroExt R M] kerIdeal R M ≃ₗ[R] M := by
  letI : Module (TrivSqZeroExt R M) M :=
    Module.compHom M (algebraMap (TrivSqZeroExt R M) R)
  letI : IsScalarTower (TrivSqZeroExt R M) R M := by
    constructor
    intro s r m
    change (s.fst * r) • m = s.fst • (r • m)
    rw [mul_smul]
  letI : TensorProduct.CompatibleSMul (TrivSqZeroExt R M) R R M :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective R M
      (fun r : R => ⟨inl r, rfl⟩)
  let equivalence : kerIdeal R M ≃ₗ[TrivSqZeroExt R M] M :=
    { (kerIdealLinearEquiv (R := R) (M := M)).toAddEquiv with
      map_smul' := by
        intro s j
        change (s * j.val).snd = s.fst • j.val.snd
        rw [(mem_kerIdeal_iff_inr R M j.val).1 j.property]
        change (s * inr j.val.snd).snd = s.fst • j.val.snd
        conv_lhs => rw [← inl_fst_add_inr_snd_eq s]
        simp [add_mul, inl_mul_inr] }
  exact equivalence.baseChange (TrivSqZeroExt R M) R (kerIdeal R M) M ≪≫ₗ
    TensorProduct.lidOfCompatibleSMul (TrivSqZeroExt R M) R M

@[simp]
theorem kerIdealBaseChange_tmul (r : R) (j : kerIdeal R M) :
    kerIdealBaseChange (R := R) (M := M) (r ⊗ₜ[TrivSqZeroExt R M] j) =
      r • kerIdealLinearEquiv (R := R) (M := M) j := by
  simp [kerIdealBaseChange, TensorProduct.lidOfCompatibleSMul_tmul,
    kerIdealLinearEquiv_apply]

@[simp]
theorem kerIdealBaseChange_symm_apply (m : M) :
    (kerIdealBaseChange (R := R) (M := M)).symm m =
      (1 : R) ⊗ₜ[TrivSqZeroExt R M]
        (kerIdealLinearEquiv (R := R) (M := M)).symm m := by
  apply (kerIdealBaseChange (R := R) (M := M)).injective
  simp

end ProjectionBaseChange

end TrivSqZeroExt
