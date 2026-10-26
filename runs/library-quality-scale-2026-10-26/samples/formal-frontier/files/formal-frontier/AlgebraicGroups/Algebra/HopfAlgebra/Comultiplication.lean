/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.Primitive
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The antipode reverses comultiplication

For a Hopf algebra over a commutative semiring, comultiplication after the
antipode is the flipped comultiplication followed by the tensor of antipodes.
The algebra need not be commutative, and the coalgebra need not be cocommutative.
Consequently, the antipode sends `(g, h)`-skew-primitive elements to
`(S h, S g)`-skew-primitive elements, without assumptions on the endpoints.

* The square of the antipode preserves comultiplication:
  `HopfAlgebra.comul_comp_antipode_comp_antipode` and
  `HopfAlgebra.comul_antipode_antipode`.

The proof compares convolution inverses of comultiplication. Mathlib supplies
the right inverse. For the left inverse we contract a right-nested fourfold
tensor, first using the middle antipode identity and counit, then the outer
antipode identity. The contraction is a composition of tensor maps and
permutations, so its linearity and scalar balancing come from the tensor
universal property, without a choice of tensor presentation.

## References

* Robert Hawkins, Mathlib, `RingTheory/Coalgebra/Primitive`: the skew-primitive
  predicate and its characteristic equations.
* Kim Morrison, Mathlib, `CategoryTheory/Monoidal/Hopf_`: the corresponding
  identity for braided Hopf objects and the convolution inverse-uniqueness proof.
* Yaël Dillies, Michał Mrugała and Yunzhou Xie, Mathlib,
  `RingTheory/HopfAlgebra/Convolution`: the concrete right convolution inverse
  of comultiplication.
* Ali Ramsey and Eric Wieser, Mathlib, `RingTheory/Coalgebra/Basic`: the
  coassociativity and counit API.
* Kenny Lau and Mario Carneiro, Mathlib, `LinearAlgebra/TensorProduct`:
  the tensor universal property, associators and permutations.
-/

@[expose] public section

universe u v

open TensorProduct WithConv
open scoped RingTheory.LinearMap

namespace HopfAlgebra

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

local notation "T" => A ⊗[R] A
local notation "Δ" => Coalgebra.comul (R := R) (A := A)
local notation "S" => antipode R (A := A)
local notation "mA" => LinearMap.mul' R A
local notation "ι" => (LinearMap.id : A →ₗ[R] A)
local notation "α₃" => LinearEquiv.toLinearMap (TensorProduct.assoc R A A A)
local notation "α₄" => LinearEquiv.toLinearMap (TensorProduct.assoc R A A T)

/-- The balanced contraction with value `S(b)c ⊗ S(a)d`. -/
private def antipodeContraction : A ⊗[R] (A ⊗[R] T) →ₗ[R] T :=
  map mA mA ∘ₗ (tensorTensorTensorComm R A A A A).toLinearMap ∘ₗ
    map (map S S ∘ₗ (TensorProduct.comm R A A).toLinearMap) LinearMap.id ∘ₗ
      (TensorProduct.assoc R A A T).symm.toLinearMap

@[simp]
private theorem antipodeContraction_tmul (a b c d : A) :
    antipodeContraction (R := R) (a ⊗ₜ (b ⊗ₜ (c ⊗ₜ d))) =
      (S b * c) ⊗ₜ (S a * d) := by
  simp [antipodeContraction]

/-- The outer contraction with value `1 ⊗ S(a)d`. -/
private def antipodeOuterContraction : T →ₗ[R] T :=
  TensorProduct.mk R A A 1 ∘ₗ mA ∘ₗ map S ι

@[simp]
private theorem antipodeOuterContraction_tmul (a d : A) :
    antipodeOuterContraction (R := R) (a ⊗ₜ d) = 1 ⊗ₜ (S a * d) := by
  simp [antipodeOuterContraction]

-- Fourfold coassociation uses naturality of the associator and triple
-- coassociation, never a permutation of coproduct factors.
private theorem comul_fourfold :
    α₄ ∘ₗ map Δ Δ ∘ₗ Δ =
      map ι (α₃ ∘ₗ map Δ ι) ∘ₗ map ι Δ ∘ₗ Δ := by
  have hn : α₄ ∘ₗ map Δ Δ =
      (map ι (map ι Δ) ∘ₗ α₃) ∘ₗ map Δ ι := by
    rw [map_map_comp_assoc_eq]
    simp only [map_id, LinearMap.comp_assoc, ← map_comp,
      LinearMap.id_comp, LinearMap.comp_id]
  have hc : α₃ ∘ₗ map Δ ι ∘ₗ Δ = map ι Δ ∘ₗ Δ :=
    Coalgebra.coassoc
  calc
    α₄ ∘ₗ map Δ Δ ∘ₗ Δ =
        map ι (map ι Δ) ∘ₗ (α₃ ∘ₗ map Δ ι ∘ₗ Δ) := by
      simpa only [LinearMap.comp_assoc] using
        congrArg (fun f => f ∘ₗ Δ) hn
    _ = map ι (map ι Δ) ∘ₗ map ι Δ ∘ₗ Δ := by rw [hc]
    _ = map ι (α₃ ∘ₗ map Δ ι) ∘ₗ map ι Δ ∘ₗ Δ := by
      simpa only [← LinearMap.comp_assoc, ← map_comp, LinearMap.id_comp]
        using congrArg (fun f : A →ₗ[R] A ⊗[R] T => map ι f ∘ₗ Δ) hc.symm

-- Contract the middle two legs using the left antipode law. Each equality
-- involving an arbitrary coproduct is obtained by tensor extensionality.
private theorem antipodeContraction_middle :
    antipodeContraction (R := R) ∘ₗ map ι (α₃ ∘ₗ map Δ ι) =
      antipodeOuterContraction (R := R) ∘ₗ
        map ι (TensorProduct.lift (LinearMap.lsmul R A ∘ₗ Coalgebra.counit)) := by
  apply TensorProduct.ext_threefold'
  intro a b d
  have h :
      antipodeContraction (R := R) ∘ₗ TensorProduct.mk R A (A ⊗[R] T) a ∘ₗ α₃ ∘ₗ
          (TensorProduct.mk R T A).flip d =
        (TensorProduct.mk R A A).flip (S a * d) ∘ₗ mA ∘ₗ map S ι := by
    apply TensorProduct.ext'
    intro p q
    simp
  have hb := LinearMap.congr_fun h (Δ b)
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.flip_apply] at hb
  rw [← LinearMap.rTensor_def, mul_antipode_rTensor_comul_apply] at hb
  simpa [LinearMap.comp_apply, map_tmul, TensorProduct.lift.tmul,
    Algebra.algebraMap_eq_smul_one, smul_tmul, tmul_smul, mul_smul_comm] using hb

private theorem antipodeContraction_left_inv :
    toConv (map S S ∘ₗ (TensorProduct.comm R A A).toLinearMap ∘ₗ Δ) * toConv Δ =
      (1 : WithConv (A →ₗ[R] T)) := by
  apply WithConv.ext
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, ofConv_toConv]
  have hm :
      LinearMap.mul' R T ∘ₗ
          map (map S S ∘ₗ (TensorProduct.comm R A A).toLinearMap) LinearMap.id =
        antipodeContraction (R := R) ∘ₗ α₄ := by
    apply TensorProduct.ext_fourfold'
    intro a b c d
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hC :
      map ι (TensorProduct.lift (LinearMap.lsmul R A ∘ₗ Coalgebra.counit)) ∘ₗ
        map ι Δ = (LinearMap.id : T →ₗ[R] T) := by
    rw [← map_comp, LinearMap.id_comp, Coalgebra.lift_lsmul_comp_counit_comp_comul,
      map_id]
  calc
    LinearMap.mul' R T ∘ₗ
        map (map S S ∘ₗ (TensorProduct.comm R A A).toLinearMap ∘ₗ Δ) Δ ∘ₗ Δ =
        antipodeContraction (R := R) ∘ₗ α₄ ∘ₗ map Δ Δ ∘ₗ Δ := by
      have hmap :
          map (map S S ∘ₗ (TensorProduct.comm R A A).toLinearMap ∘ₗ Δ) Δ =
            map (map S S ∘ₗ (TensorProduct.comm R A A).toLinearMap) LinearMap.id ∘ₗ
              map Δ Δ := by
        simpa only [LinearMap.id_comp, LinearMap.comp_assoc] using
          (map_comp (map S S ∘ₗ (TensorProduct.comm R A A).toLinearMap)
            (LinearMap.id : T →ₗ[R] T) Δ Δ)
      rw [hmap]
      simpa only [LinearMap.comp_assoc] using
        congrArg (fun f => f ∘ₗ map Δ Δ ∘ₗ Δ) hm
    _ = antipodeContraction (R := R) ∘ₗ
        map ι (α₃ ∘ₗ map Δ ι) ∘ₗ map ι Δ ∘ₗ Δ := by
      simpa only [LinearMap.comp_assoc] using
        congrArg (fun f => antipodeContraction (R := R) ∘ₗ f)
          (comul_fourfold (R := R) (A := A))
    _ = antipodeOuterContraction (R := R) ∘ₗ Δ := by
      have hmiddle := congrArg (fun f => f ∘ₗ map ι Δ ∘ₗ Δ)
        (antipodeContraction_middle (R := R) (A := A))
      have hcounit := congrArg (fun f => antipodeOuterContraction (R := R) ∘ₗ f ∘ₗ Δ) hC
      simp only [LinearMap.comp_assoc] at hmiddle hcounit
      simpa only [LinearMap.id_comp] using hmiddle.trans hcounit
    _ = Algebra.linearMap R T ∘ₗ Coalgebra.counit := by
      have ha : mA ∘ₗ map S ι ∘ₗ Δ =
          Algebra.linearMap R A ∘ₗ Coalgebra.counit :=
        mul_antipode_rTensor_comul
      calc
        antipodeOuterContraction (R := R) ∘ₗ Δ =
            TensorProduct.mk R A A 1 ∘ₗ (mA ∘ₗ map S ι ∘ₗ Δ) := rfl
        _ = TensorProduct.mk R A A 1 ∘ₗ (Algebra.linearMap R A ∘ₗ Coalgebra.counit) := by rw [ha]
        _ = Algebra.linearMap R T ∘ₗ Coalgebra.counit := by
          ext x
          simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]

/-- The antipode reverses comultiplication, with no commutativity or
cocommutativity assumption. This is the concrete form of Mathlib's
`CategoryTheory.HopfObj.antipode_comul`, proved by convolution inverse uniqueness. -/
theorem comul_comp_antipode :
    Δ ∘ₗ S = map S S ∘ₗ (TensorProduct.comm R A A).toLinearMap ∘ₗ Δ := by
  exact (toConv_injective
    (left_inv_eq_right_inv antipodeContraction_left_inv LinearMap.comul_right_inv)).symm

/-- Comultiplication of an antipode is the flipped tensor of antipodes applied
to comultiplication. -/
@[simp]
theorem comul_antipode (x : A) :
    Δ (S x) = map S S (TensorProduct.comm R A A (Δ x)) :=
  LinearMap.congr_fun comul_comp_antipode x

/-- The square of the antipode preserves comultiplication, with no commutativity
or cocommutativity assumption. -/
theorem comul_comp_antipode_comp_antipode :
    Δ ∘ₗ (S ∘ₗ S) = map (S ∘ₗ S) (S ∘ₗ S) ∘ₗ Δ := by
  ext x
  simp only [LinearMap.comp_apply, comul_antipode, ← map_comm, comm_comm, map_map]

/-- Comultiplication of the square of the antipode is the tensor of its square
applied to comultiplication. -/
@[simp]
theorem comul_antipode_antipode (x : A) :
    Δ (S (S x)) = map (S ∘ₗ S) (S ∘ₗ S) (Δ x) :=
  LinearMap.congr_fun comul_comp_antipode_comp_antipode x

end HopfAlgebra

namespace Coalgebra.IsSkewPrimitiveElem

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  {g h a : A}

/-- The antipode reverses the endpoints of a skew-primitive element.
No group-like or unit hypotheses on the endpoints are required. -/
lemma antipode (ha : IsSkewPrimitiveElem R g h a) :
    IsSkewPrimitiveElem R (HopfAlgebra.antipode R h) (HopfAlgebra.antipode R g)
      (HopfAlgebra.antipode R a) where
  counit_eq_zero := by rw [HopfAlgebra.counit_antipode, ha.counit_eq_zero]
  comul_eq_tmul_add_tmul := by
    rw [HopfAlgebra.comul_antipode, ha.comul_eq_tmul_add_tmul]
    simp only [map_add, _root_.TensorProduct.comm_tmul, _root_.TensorProduct.map_tmul,
      add_comm]

end Coalgebra.IsSkewPrimitiveElem
