/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom
public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Group-like elements of tensor products

For coalgebras `C` and `D` over a commutative semiring `R`, normalized group-like elements
of `C ⊗[R] D` correspond to pairs of group-like elements of the factors. The forward maps
apply the counit of the other factor, followed by the appropriate tensor unitor. The inverse
uses the scalar-source correspondence of `GroupLike.coalgHomEquiv` and the tensor product
of coalgebra morphisms; its underlying value is the pure tensor of the two given values.

Reconstruction follows by contracting the comultiplication with the two counit projections.
The proof uses only linear tensor maps and the two counit laws, not cocommutativity or
injectivity of pure tensors. The factors need no multiplication, and the scalar semiring
need not be nontrivial. In particular, normalization does not assert that a value is nonzero.

## References

This construction builds on the scalar-source point correspondence and transport in
`AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom`. It uses the group-like formalization of
Yaël Dillies and Michał Mrugała in Mathlib, the tensor-coalgebra infrastructure of
Amelia Livingston and Andrew Yang, and Mathlib's linear tensor maps, unitors and counit laws.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uD uC' uD'

namespace GroupLike

variable {R : Type uR} {C : Type uC} {D : Type uD}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

local notation "πC" =>
  (CoalgHom.comp (CoalgEquiv.toCoalgHom (Coalgebra.TensorProduct.rid R R C))
    (Coalgebra.TensorProduct.map
      (CoalgHom.id R C) (Coalgebra.counitCoalgHom R D)))

local notation "πD" =>
  (CoalgHom.comp (CoalgEquiv.toCoalgHom (Coalgebra.TensorProduct.lid R D))
    (Coalgebra.TensorProduct.map
      (Coalgebra.counitCoalgHom R C) (CoalgHom.id R D)))

-- On four pure factors the crossed counits can be moved between the tensor factors.
-- After comultiplication this is the right counit law on C and the left counit law on D.
private theorem counit_tensor_contraction :
    (TensorProduct.map (πC).toLinearMap (πD).toLinearMap).comp
      (Coalgebra.comul (R := R) (A := C ⊗[R] D)) = LinearMap.id := by
  let f : C ⊗[R] C →ₗ[R] C :=
    (TensorProduct.rid R C).toLinearMap.comp
      ((Coalgebra.counit (R := R) (A := C)).lTensor C)
  let g : D ⊗[R] D →ₗ[R] D :=
    (TensorProduct.lid R D).toLinearMap.comp
      ((Coalgebra.counit (R := R) (A := D)).rTensor D)
  have h :
      (TensorProduct.map (πC).toLinearMap (πD).toLinearMap).comp
          (TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap =
        TensorProduct.map f g := by
    apply TensorProduct.ext_fourfold'
    intro c₁ c₂ d₁ d₂
    change
      (Coalgebra.counit (R := R) d₁ • c₁) ⊗ₜ[R]
          (Coalgebra.counit (R := R) c₂ • d₂) =
        (Coalgebra.counit (R := R) c₂ • c₁) ⊗ₜ[R]
          (Coalgebra.counit (R := R) d₁ • d₂)
    simp only [TensorProduct.smul_tmul_smul, mul_comm]
  apply TensorProduct.ext'
  intro c d
  change TensorProduct.map (πC).toLinearMap (πD).toLinearMap
    (Coalgebra.comul (R := R) (c ⊗ₜ[R] d)) = c ⊗ₜ[R] d
  rw [TensorProduct.comul_tmul,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq]
  change
    ((TensorProduct.map (πC).toLinearMap (πD).toLinearMap).comp
      (TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap)
        (Coalgebra.comul (R := R) c ⊗ₜ[R] Coalgebra.comul (R := R) d) = c ⊗ₜ[R] d
  rw [h, TensorProduct.map_tmul]
  change
    TensorProduct.rid R C
        ((Coalgebra.counit (R := R) (A := C)).lTensor C
          (Coalgebra.comul (R := R) c)) ⊗ₜ[R]
      TensorProduct.lid R D
        ((Coalgebra.counit (R := R) (A := D)).rTensor D
          (Coalgebra.comul (R := R) d)) = c ⊗ₜ[R] d
  rw [Coalgebra.lTensor_counit_comul, Coalgebra.rTensor_counit_comul]
  simp only [TensorProduct.rid_tmul, TensorProduct.lid_tmul, one_smul]

variable (R C D) in
/-- Normalized group-like elements of a tensor product correspond to ordered pairs of
normalized group-like elements. The projections apply the opposite counit and a tensor
unitor; the inverse tensors the scalar-source point morphisms. -/
noncomputable def tensorEquiv :
    GroupLike R (C ⊗[R] D) ≃ GroupLike R C × GroupLike R D where
  toFun x := (GroupLike.map πC x, GroupLike.map πD x)
  invFun p :=
    (GroupLike.coalgHomEquiv (R := R) (C := C ⊗[R] D)).symm
      ((Coalgebra.TensorProduct.map
          (GroupLike.coalgHomEquiv (R := R) (C := C) p.1)
          (GroupLike.coalgHomEquiv (R := R) (C := D) p.2)).comp
        (Coalgebra.TensorProduct.lid R R).symm.toCoalgHom)
  left_inv x := by
    apply GroupLike.ext
    change ((1 : R) • πC x.val) ⊗ₜ[R] ((1 : R) • πD x.val) = x.val
    simp only [one_smul]
    have h := LinearMap.congr_fun
      (counit_tensor_contraction (R := R) (C := C) (D := D)) x.val
    simpa only [CoalgHom.toLinearMap_eq_coe, CoalgHom.coe_toLinearMap,
      LinearMap.comp_apply, LinearMap.id_apply,
      x.isGroupLikeElem_val.comul_eq_tmul_self, TensorProduct.map_tmul] using h
  right_inv p := by
    apply Prod.ext
    · apply GroupLike.ext
      change πC (((1 : R) • p.1.val) ⊗ₜ[R] ((1 : R) • p.2.val)) = p.1.val
      simp only [one_smul]
      change Coalgebra.counit (R := R) p.2.val • p.1.val = p.1.val
      rw [p.2.isGroupLikeElem_val.counit_eq_one, one_smul]
    · apply GroupLike.ext
      change πD (((1 : R) • p.1.val) ⊗ₜ[R] ((1 : R) • p.2.val)) = p.2.val
      simp only [one_smul]
      change Coalgebra.counit (R := R) p.1.val • p.2.val = p.2.val
      rw [p.1.isGroupLikeElem_val.counit_eq_one, one_smul]

/-- The first component applies the counit of `D` and the right tensor unitor. -/
@[simp]
theorem tensorEquiv_apply_fst (x : GroupLike R (C ⊗[R] D)) :
    (tensorEquiv R C D x).1 = GroupLike.map πC x := rfl

/-- The second component applies the counit of `C` and the left tensor unitor. -/
@[simp]
theorem tensorEquiv_apply_snd (x : GroupLike R (C ⊗[R] D)) :
    (tensorEquiv R C D x).2 = GroupLike.map πD x := rfl

/-- The inverse correspondence has underlying value the pure tensor of the given values. -/
@[simp]
theorem tensorEquiv_symm_val (p : GroupLike R C × GroupLike R D) :
    ((tensorEquiv R C D).symm p).val = p.1.val ⊗ₜ[R] p.2.val := by
  change ((1 : R) • p.1.val) ⊗ₜ[R] ((1 : R) • p.2.val) = p.1.val ⊗ₜ[R] p.2.val
  simp only [one_smul]

/-- An ordered pair is the decomposition of a group-like tensor exactly when its values
have that tensor as their pure tensor. Together with equivalence injectivity, this gives
existence and uniqueness of the normalized ordered decomposition. -/
theorem tensorEquiv_apply_eq_iff (x : GroupLike R (C ⊗[R] D))
    (c : GroupLike R C) (d : GroupLike R D) :
    tensorEquiv R C D x = (c, d) ↔ x.val = c.val ⊗ₜ[R] d.val := by
  constructor
  · intro h
    have hv := congrArg (fun p => ((tensorEquiv R C D).symm p).val) h
    simpa only [Equiv.symm_apply_apply, tensorEquiv_symm_val] using hv
  · intro h
    have hx : x = (tensorEquiv R C D).symm (c, d) := by
      apply GroupLike.ext
      simpa only [tensorEquiv_symm_val] using h
    rw [hx, Equiv.apply_symm_apply]

variable {C' : Type uC'} {D' : Type uD'}
variable [AddCommMonoid C'] [Module R C'] [Coalgebra R C']
variable [AddCommMonoid D'] [Module R D'] [Coalgebra R D']

local notation "πC'" =>
  (CoalgHom.comp (CoalgEquiv.toCoalgHom (Coalgebra.TensorProduct.rid R R C'))
    (Coalgebra.TensorProduct.map
      (CoalgHom.id R C') (Coalgebra.counitCoalgHom R D')))

local notation "πD'" =>
  (CoalgHom.comp (CoalgEquiv.toCoalgHom (Coalgebra.TensorProduct.lid R D'))
    (Coalgebra.TensorProduct.map
      (Coalgebra.counitCoalgHom R C') (CoalgHom.id R D')))

/-- The tensor decomposition is natural under independently chosen coalgebra morphisms
on the two factors. -/
theorem tensorEquiv_mapCoalgHoms (f : C →ₗc[R] C') (g : D →ₗc[R] D')
    (x : GroupLike R (C ⊗[R] D)) :
    tensorEquiv R C' D' (GroupLike.map (Coalgebra.TensorProduct.map f g) x) =
      (GroupLike.map f ((tensorEquiv R C D x).1),
       GroupLike.map g ((tensorEquiv R C D x).2)) := by
  apply Prod.ext
  · apply GroupLike.ext
    change πC' (Coalgebra.TensorProduct.map f g x.val) = f (πC x.val)
    have h : (πC').toLinearMap.comp (Coalgebra.TensorProduct.map f g).toLinearMap =
        f.toLinearMap.comp (πC).toLinearMap := by
      apply TensorProduct.ext'
      intro c d
      change Coalgebra.counit (R := R) (g d) • f c =
        f (Coalgebra.counit (R := R) d • c)
      rw [CoalgHomClass.counit_comp_apply, map_smul]
    exact LinearMap.congr_fun h x.val
  · apply GroupLike.ext
    change πD' (Coalgebra.TensorProduct.map f g x.val) = g (πD x.val)
    have h : (πD').toLinearMap.comp (Coalgebra.TensorProduct.map f g).toLinearMap =
        g.toLinearMap.comp (πD).toLinearMap := by
      apply TensorProduct.ext'
      intro c d
      change Coalgebra.counit (R := R) (f c) • g d =
        g (Coalgebra.counit (R := R) c • d)
      rw [CoalgHomClass.counit_comp_apply, map_smul]
    exact LinearMap.congr_fun h x.val

end GroupLike
