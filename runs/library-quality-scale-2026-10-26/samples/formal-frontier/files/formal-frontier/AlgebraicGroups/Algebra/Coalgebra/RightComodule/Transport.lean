/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Transport of specified right comodules along linear equivalences

`Coalgebra.RightComodule.transport` changes the module carrying a specified
right coaction along an `R`-linear equivalence `e : V ≃ₗ[R] W`. The coalgebra
`C` and all given additive and scalar-module structures remain fixed. The new
coaction is `(e tensor id_C) ∘ ρ ∘ e.symm`: only the first tensor factor changes.

The constructor works over a commutative semiring, for additive commutative
monoid modules, with independent universes for the scalars, coalgebra and two
carriers. It needs no flatness, projectivity, basis or finiteness assumption.
`transport_coaction` and `transport_coaction_apply` read back its coaction.

`transportHom` and `transportInvHom` are the canonical colinear maps with
underlying linear maps `e` and `e.symm`; their composites are the respective
identities. Transport respects identity, successive carrier equivalences and
inverses as equalities of specified comodule structures. The universal property
`transport_eq_iff_colinear` characterizes the transported target by colinearity
of `e`. These are object-coherence laws and a canonical inverse pair, not a
construction on arbitrary comodule morphisms.

## References

Mathlib supplies `LinearEquiv.arrowCongr`, tensor extensions, associators,
unitors and their naturality laws. The construction retains the earlier
project raw-conjugation and tensor-naturality proof approach for specified
right comodules, including its closed coassociativity and counit arguments.
The canonical colinear pair and object-coherence proofs use Mathlib's
linear-equivalence inverse and tensor-composition laws.
-/

@[expose] public section

universe uR uC uV uW uZ

open scoped TensorProduct

namespace Coalgebra.RightComodule

noncomputable section

section Conjugation

variable {R : Type uR} {C : Type uC} {V : Type uV} {W : Type uW}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Conjugation of a specified coaction, changing only its module factor. -/
private def conjugatedCoaction (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    W →ₗ[R] W ⊗[R] C :=
  LinearEquiv.arrowCongr e (e.rTensor C) X.coaction

private theorem conjugatedCoaction_coassoc (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (TensorProduct.assoc R W C C).toLinearMap ∘ₗ (conjugatedCoaction X e).rTensor C ∘ₗ
        conjugatedCoaction X e =
      (comul (R := R) (A := C)).lTensor W ∘ₗ conjugatedCoaction X e := by
  have hconj (w : W) : conjugatedCoaction X e w =
      e.toLinearMap.rTensor C (X.coaction (e.symm w)) := by
    rfl
  have hcolinear : conjugatedCoaction X e ∘ₗ e.toLinearMap =
      e.toLinearMap.rTensor C ∘ₗ X.coaction := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hconj,
      LinearEquiv.symm_apply_apply]
  have htensor : (conjugatedCoaction X e).rTensor C ∘ₗ e.toLinearMap.rTensor C =
      (e.toLinearMap.rTensor C).rTensor C ∘ₗ X.coaction.rTensor C := by
    rw [← LinearMap.rTensor_comp, hcolinear, LinearMap.rTensor_comp]
  have hassoc : (TensorProduct.assoc R W C C).toLinearMap ∘ₗ
        (e.toLinearMap.rTensor C).rTensor C =
      e.toLinearMap.rTensor (C ⊗[R] C) ∘ₗ (TensorProduct.assoc R V C C).toLinearMap := by
    simpa only [LinearMap.rTensor_def, TensorProduct.map_id] using
      (TensorProduct.map_map_comp_assoc_eq e.toLinearMap
        (LinearMap.id : C →ₗ[R] C) (LinearMap.id : C →ₗ[R] C)).symm
  have hcomul : e.toLinearMap.rTensor (C ⊗[R] C) ∘ₗ (comul (R := R) (A := C)).lTensor V =
      (comul (R := R) (A := C)).lTensor W ∘ₗ e.toLinearMap.rTensor C := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  ext w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hconj]
  calc
    TensorProduct.assoc R W C C
        ((conjugatedCoaction X e).rTensor C
          (e.toLinearMap.rTensor C (X.coaction (e.symm w)))) =
        TensorProduct.assoc R W C C
          ((e.toLinearMap.rTensor C).rTensor C
            (X.coaction.rTensor C (X.coaction (e.symm w)))) := by
      congr 1
      exact LinearMap.congr_fun htensor (X.coaction (e.symm w))
    _ = e.toLinearMap.rTensor (C ⊗[R] C)
        (TensorProduct.assoc R V C C
          (X.coaction.rTensor C (X.coaction (e.symm w)))) :=
      LinearMap.congr_fun hassoc (X.coaction.rTensor C (X.coaction (e.symm w)))
    _ = e.toLinearMap.rTensor (C ⊗[R] C)
        ((comul (R := R) (A := C)).lTensor V (X.coaction (e.symm w))) := by
      rw [X.coassoc_apply]
    _ = (comul (R := R) (A := C)).lTensor W
        (e.toLinearMap.rTensor C (X.coaction (e.symm w))) :=
      LinearMap.congr_fun hcomul (X.coaction (e.symm w))

private theorem conjugatedCoaction_counit_comp (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (counit (R := R) (A := C)).lTensor W ∘ₗ conjugatedCoaction X e =
      (TensorProduct.rid R W).symm.toLinearMap := by
  have hnatural :
      (counit (R := R) (A := C)).lTensor W ∘ₗ (e.rTensor C).toLinearMap =
        (e.rTensor R).toLinearMap ∘ₗ (counit (R := R) (A := C)).lTensor V := by
    simp only [LinearEquiv.coe_rTensor, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, conjugatedCoaction, LinearEquiv.arrowCongr_apply,
    LinearEquiv.coe_coe]
  calc
    (counit (R := R) (A := C)).lTensor W ((e.rTensor C) (X.coaction (e.symm w))) =
        (e.rTensor R)
          ((counit (R := R) (A := C)).lTensor V (X.coaction (e.symm w))) :=
      LinearMap.congr_fun hnatural _
    _ = (e.rTensor R) ((TensorProduct.rid R V).symm (e.symm w)) :=
      congrArg (e.rTensor R) (LinearMap.congr_fun X.counit_comp (e.symm w))
    _ = (TensorProduct.rid R W).symm w := by
      simp only [TensorProduct.rid_symm_apply, LinearEquiv.rTensor_tmul,
        LinearEquiv.apply_symm_apply]


/-- Transport a specified right `C`-comodule along an `R`-linear equivalence of
its carrier, keeping `C` and the given module structures fixed. -/
@[no_expose]
def transport (X : RightComodule R C V) (e : V ≃ₗ[R] W) : RightComodule R C W where
  coaction := conjugatedCoaction X e
  coassoc := conjugatedCoaction_coassoc X e
  counit_comp := conjugatedCoaction_counit_comp X e

/-- The transported coaction is arrow congruence on the source coaction,
with the equivalence extended only on the module tensor factor. -/
theorem transport_coaction (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (X.transport e).coaction = LinearEquiv.arrowCongr e (e.rTensor C) X.coaction := (rfl)

/-- At a target vector, transport first applies the inverse carrier equivalence,
then the original coaction, then the equivalence on the first tensor factor. -/
theorem transport_coaction_apply (X : RightComodule R C V) (e : V ≃ₗ[R] W) (w : W) :
    (X.transport e).coaction w = e.toLinearMap.rTensor C (X.coaction (e.symm w)) := (rfl)

/-- The carrier equivalence as a colinear map to the transported comodule. -/
@[no_expose]
def transportHom (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    RightComoduleHom X (X.transport e) where
  toLinearMap := e.toLinearMap
  colinear := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, transport_coaction_apply,
      LinearEquiv.symm_apply_apply]

/-- The underlying linear map of the canonical forward colinear map. -/
@[simp] theorem transportHom_toLinearMap (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (transportHom X e).toLinearMap = e.toLinearMap := (rfl)

/-- The canonical forward colinear map has the carrier equivalence as its function. -/
@[simp] theorem coe_transportHom (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (transportHom X e : V → W) = (e : V → W) := (rfl)

/-- Evaluation of the canonical forward colinear map. -/
@[simp] theorem transportHom_apply (X : RightComodule R C V) (e : V ≃ₗ[R] W) (v : V) :
    transportHom X e v = e v := (rfl)

/-- The inverse carrier equivalence as a colinear map from the transported comodule. -/
@[no_expose]
def transportInvHom (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    RightComoduleHom (X.transport e) X where
  toLinearMap := e.symm.toLinearMap
  colinear := by
    ext w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, transport_coaction_apply]
    rw [← LinearMap.rTensor_comp_apply, LinearEquiv.symm_comp,
      LinearMap.rTensor_id, LinearMap.id_apply]

/-- The underlying linear map of the canonical inverse colinear map. -/
@[simp] theorem transportInvHom_toLinearMap (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (transportInvHom X e).toLinearMap = e.symm.toLinearMap := (rfl)

/-- The canonical inverse colinear map has the inverse carrier equivalence as its function. -/
@[simp] theorem coe_transportInvHom (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (transportInvHom X e : W → V) = (e.symm : W → V) := (rfl)

/-- Evaluation of the canonical inverse colinear map. -/
@[simp] theorem transportInvHom_apply (X : RightComodule R C V) (e : V ≃ₗ[R] W) (w : W) :
    transportInvHom X e w = e.symm w := (rfl)

/-- The inverse after the forward map is the identity on the original comodule. -/
@[simp] theorem transportInvHom_comp_transportHom
    (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (transportInvHom X e).comp (transportHom X e) = RightComoduleHom.id X := by
  ext v
  simp only [RightComoduleHom.comp_apply, transportInvHom_apply, transportHom_apply,
    LinearEquiv.symm_apply_apply, RightComoduleHom.id_apply]

/-- The forward after the inverse map is the identity on the transported comodule. -/
@[simp] theorem transportHom_comp_transportInvHom
    (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (transportHom X e).comp (transportInvHom X e) = RightComoduleHom.id (X.transport e) := by
  ext w
  simp only [RightComoduleHom.comp_apply, transportHom_apply, transportInvHom_apply,
    LinearEquiv.apply_symm_apply, RightComoduleHom.id_apply]

/-- Transport along the identity leaves the specified comodule unchanged. -/
@[simp] theorem transport_refl (X : RightComodule R C V) :
    X.transport (LinearEquiv.refl R V) = X := by
  apply RightComodule.ext
  ext v
  simp only [transport_coaction, LinearEquiv.arrowCongr_apply, LinearEquiv.rTensor_refl,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply]

/-- Successive carrier transport along `e` and then `f` agrees with their composite. -/
theorem transport_trans {Z : Type uZ} [AddCommMonoid Z] [Module R Z]
    (X : RightComodule R C V) (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] Z) :
    (X.transport e).transport f = X.transport (e.trans f) := by
  apply RightComodule.ext
  ext z
  simp only [transport_coaction, LinearEquiv.arrowCongr_apply, LinearEquiv.rTensor_trans,
    LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]

/-- Transporting back along the inverse recovers the original specified comodule. -/
@[simp] theorem transport_symm (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    (X.transport e).transport e.symm = X := by
  rw [transport_trans, LinearEquiv.self_trans_symm, transport_refl]

/-- A lawful target coaction is the transported one exactly when the carrier
equivalence intertwines it with the original coaction. -/
theorem transport_eq_iff_colinear (X : RightComodule R C V) (e : V ≃ₗ[R] W)
    (Y : RightComodule R C W) :
    X.transport e = Y ↔
      Y.coaction ∘ₗ e.toLinearMap = e.toLinearMap.rTensor C ∘ₗ X.coaction := by
  constructor
  · intro h
    subst Y
    simpa only [transportHom_toLinearMap] using (transportHom X e).colinear
  · intro h
    apply RightComodule.ext
    ext w
    rw [transport_coaction_apply]
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      (LinearMap.congr_fun h (e.symm w)).symm

end Conjugation

end

end Coalgebra.RightComodule
