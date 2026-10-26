/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Group-like equations under extension of scalars

The equations `ε(c) = 1` and `Δ(c) = c ⊗ c` are preserved by extension of
scalars along an algebra of commutative semirings. A faithfully flat algebra
of commutative rings reflects both equations. These fieldwise statements
require only `CoalgebraStruct`, not coassociativity or counit laws.

The scalar extension uses the tensor-product coalgebra structure on
`S ⊗[R] C`, with its usual left `S`-module structure. The corresponding
statements for `IsGroupLikeElem` assume a full coalgebra, as required by
that predicate's interface.

## Implementation notes

Reflection is presented for an additive commutative group, matching the
faithfully flat tensor-injectivity API. It does not assume flatness,
projectivity, finite generation or nontriviality of `C`. The scalar and
carrier universes are independent.

## References

Mathlib supplies the group-like predicate, the tensor-product coalgebra
structure and pure-tensor formulas in `Mathlib.RingTheory.Coalgebra.GroupLike`
and `Mathlib.RingTheory.Coalgebra.TensorProduct`, the comparison equivalence
`TensorProduct.AlgebraTensorModule.distribBaseChange` in
`Mathlib.LinearAlgebra.TensorProduct.Tower`, and faithfully flat unit-tensor
injectivity in `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra

/-- Comultiplication on a scalar-extension pure tensor is the base-changed
comultiplication followed by the tensor-product comparison equivalence. -/
theorem comul_baseChange_tmul
    (R : Type u) (S : Type v) {C : Type w}
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]
    (s : S) (c : C) :
    comul (R := S) (s ⊗ₜ[R] c) =
      TensorProduct.AlgebraTensorModule.distribBaseChange R S C C
        (s ⊗ₜ[R] comul (R := R) c) := by
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange R S C C).symm.injective
  rw [LinearEquiv.symm_apply_apply, TensorProduct.comul_tmul,
    CommSemiring.comul_apply]
  induction (comul (R := R) c) using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul]
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- Extension of scalars preserves the counit-one and tensor-square equations
using only the comultiplication and counit data. -/
theorem baseChange_counit_eq_one_and_comul_eq_tmul_self
    (R : Type u) (S : Type v) {C : Type w}
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]
    (c : C) (hε : counit (R := R) c = 1)
    (hΔ : comul (R := R) c = c ⊗ₜ[R] c) :
    counit (R := S) ((1 : S) ⊗ₜ[R] c) = 1 ∧
      comul (R := S) ((1 : S) ⊗ₜ[R] c) =
        ((1 : S) ⊗ₜ[R] c) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] c) := by
  constructor
  · simp only [TensorProduct.counit_tmul, CommSemiring.counit_apply, hε, one_smul]
  · rw [comul_baseChange_tmul, hΔ,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

/-- A faithfully flat scalar extension detects the counit-one and tensor-square
equations. Only comultiplication and counit data on `C` are required. -/
theorem baseChange_counit_eq_one_and_comul_eq_tmul_self_iff
    (R : Type u) (S : Type v) {C : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup C] [Module R C] [CoalgebraStruct R C]
    [Module.FaithfullyFlat R S] (c : C) :
    (counit (R := S) ((1 : S) ⊗ₜ[R] c) = 1 ∧
      comul (R := S) ((1 : S) ⊗ₜ[R] c) =
        ((1 : S) ⊗ₜ[R] c) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] c)) ↔
      (counit (R := R) c = 1 ∧ comul (R := R) c = c ⊗ₜ[R] c) := by
  constructor
  · rintro ⟨hε, hΔ⟩
    constructor
    · apply FaithfulSMul.algebraMap_injective R S
      simpa only [TensorProduct.counit_tmul, CommSemiring.counit_apply,
        Algebra.smul_def, mul_one, map_one] using hε
    · apply Module.FaithfullyFlat.tensorProduct_mk_injective
        (A := R) (B := S) (C ⊗[R] C)
      have h := congrArg
        (TensorProduct.AlgebraTensorModule.distribBaseChange R S C C).symm hΔ
      simpa only [comul_baseChange_tmul, LinearEquiv.symm_apply_apply,
        TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
        one_mul, TensorProduct.mk_apply] using h
  · rintro ⟨hε, hΔ⟩
    exact baseChange_counit_eq_one_and_comul_eq_tmul_self R S c hε hΔ

end Coalgebra

/-- A group-like element remains group-like after extension of scalars, for the
tensor-product coalgebra structure. -/
theorem IsGroupLikeElem.baseChange
    {R : Type u} (S : Type v) {C : Type w}
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid C] [Module R C] [Coalgebra R C]
    {c : C} (hc : IsGroupLikeElem R c) :
    IsGroupLikeElem S ((1 : S) ⊗ₜ[R] c) := by
  exact (isGroupLikeElem_iff S _).2
    (Coalgebra.baseChange_counit_eq_one_and_comul_eq_tmul_self R S c
      hc.counit_eq_one hc.comul_eq_tmul_self)

/-- Faithfully flat extension of scalars detects group-like elements of a
coalgebra. -/
theorem isGroupLikeElem_baseChange_iff
    (R : Type u) (S : Type v) {C : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup C] [Module R C] [Coalgebra R C]
    [Module.FaithfullyFlat R S] (c : C) :
    IsGroupLikeElem S ((1 : S) ⊗ₜ[R] c) ↔ IsGroupLikeElem R c := by
  rw [isGroupLikeElem_iff, isGroupLikeElem_iff]
  exact Coalgebra.baseChange_counit_eq_one_and_comul_eq_tmul_self_iff R S c
