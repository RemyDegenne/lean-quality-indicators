/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Coalgebra data along a linear equivalence

Mathlib defines `LinearEquiv.coalgebraStruct` and `LinearEquiv.coalgebra` by transporting
comultiplication and counit along a linear equivalence. This file records their formulas
as equalities of linear maps and on individual elements. The structure being projected
is explicit, so these formulas do not require a coalgebra instance on the source module.

The data formulas only require a commutative semiring and additive commutative monoids.
The formulas for `LinearEquiv.coalgebra` use the same data formulas when the target is a
coalgebra.

For example, a pure-tensor expression in the target gives a pure-tensor expression in
the source. Under the module hypotheses below, one can write:

```lean
example [Coalgebra R B] (e : A ≃ₗ[R] B) (x : A) (b₁ b₂ : B)
    (h : Coalgebra.comul (R := R) (e x) = b₁ ⊗ₜ[R] b₂) :
    @CoalgebraStruct.comul R A _ _ _ (e.coalgebra R).toCoalgebraStruct x =
      e.symm b₁ ⊗ₜ[R] e.symm b₂ := by
  rw [LinearEquiv.coalgebra_comul_apply, h, TensorProduct.map_tmul]
```

## References

`Mathlib.RingTheory.Coalgebra.Basic` defines both transported structures, including
coassociativity and the two counitality laws for `LinearEquiv.coalgebra`.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace LinearEquiv

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]

/-- Comultiplication in the transported data is conjugated by the linear equivalence
and the tensor product of its inverse. -/
@[simp]
theorem coalgebraStruct_comul [CoalgebraStruct R B] (e : A ≃ₗ[R] B) :
    @CoalgebraStruct.comul R A _ _ _ (e.coalgebraStruct R) =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := B) ∘ₗ e.toLinearMap :=
  rfl

/-- The counit in the transported data is the target counit composed with the
linear equivalence. -/
@[simp]
theorem coalgebraStruct_counit [CoalgebraStruct R B] (e : A ≃ₗ[R] B) :
    @CoalgebraStruct.counit R A _ _ _ (e.coalgebraStruct R) =
      Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap :=
  rfl

/-- Transported comultiplication applies the tensor product of the inverse equivalence
to the comultiplication of the image. -/
@[simp]
theorem coalgebraStruct_comul_apply [CoalgebraStruct R B] (e : A ≃ₗ[R] B) (x : A) :
    @CoalgebraStruct.comul R A _ _ _ (e.coalgebraStruct R) x =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
        (Coalgebra.comul (R := R) (A := B) (e x)) :=
  LinearMap.congr_fun (coalgebraStruct_comul e) x

/-- The transported counit agrees with the target counit on the image. -/
@[simp]
theorem coalgebraStruct_counit_apply [CoalgebraStruct R B] (e : A ≃ₗ[R] B) (x : A) :
    @CoalgebraStruct.counit R A _ _ _ (e.coalgebraStruct R) x =
      Coalgebra.counit (R := R) (A := B) (e x) :=
  LinearMap.congr_fun (coalgebraStruct_counit e) x

/-- Comultiplication of the transported coalgebra is conjugated by the linear equivalence
and the tensor product of its inverse. -/
@[simp]
theorem coalgebra_comul [Coalgebra R B] (e : A ≃ₗ[R] B) :
    @CoalgebraStruct.comul R A _ _ _ (e.coalgebra R).toCoalgebraStruct =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := B) ∘ₗ e.toLinearMap :=
  coalgebraStruct_comul e

/-- The counit of the transported coalgebra is the target counit composed with the
linear equivalence. -/
@[simp]
theorem coalgebra_counit [Coalgebra R B] (e : A ≃ₗ[R] B) :
    @CoalgebraStruct.counit R A _ _ _ (e.coalgebra R).toCoalgebraStruct =
      Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap :=
  coalgebraStruct_counit e

/-- Comultiplication of the transported coalgebra applies the tensor product of the inverse
equivalence to the comultiplication of the image. -/
@[simp]
theorem coalgebra_comul_apply [Coalgebra R B] (e : A ≃ₗ[R] B) (x : A) :
    @CoalgebraStruct.comul R A _ _ _ (e.coalgebra R).toCoalgebraStruct x =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
        (Coalgebra.comul (R := R) (A := B) (e x)) :=
  coalgebraStruct_comul_apply e x

/-- The counit of the transported coalgebra agrees with the target counit on the image. -/
@[simp]
theorem coalgebra_counit_apply [Coalgebra R B] (e : A ≃ₗ[R] B) (x : A) :
    @CoalgebraStruct.counit R A _ _ _ (e.coalgebra R).toCoalgebraStruct x =
      Coalgebra.counit (R := R) (A := B) (e x) :=
  coalgebraStruct_counit_apply e x

end LinearEquiv
