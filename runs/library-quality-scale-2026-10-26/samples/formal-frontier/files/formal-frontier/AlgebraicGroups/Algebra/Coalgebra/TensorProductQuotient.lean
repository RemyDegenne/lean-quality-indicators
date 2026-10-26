/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Coideals defining tensor products of coalgebra quotients

For coideals `p` of `C` and `q` of `D`, the sum of the images of `p ⊗[R] D`
and `C ⊗[R] q` in `C ⊗[R] D` is a coideal. The statement uses the submodule
appearing in `TensorProduct.quotientTensorQuotientEquiv`.

`TensorProduct.quotientTensorQuotientCoalgEquiv` refines that linear equivalence
on the same quotient carriers with their canonical coalgebra structures. Its
representative formulas, quotient-map square and unique factorization property
identify coalgebra maps from the tensor product of the two quotients.

Only coalgebra structures are needed, not coassociativity or the counit laws.
The argument uses the existing quotient structures on `C ⧸ p` and `D ⧸ q`,
together with the linear quotient comparison. It does not assume a coalgebra
structure on the quotient by the sum while proving that sum is a coideal.

## References

Mathlib supplies the linear quotient comparison in
`Mathlib.LinearAlgebra.TensorProduct.Quotient`, the canonical quotient coalgebra
structures in `Mathlib.RingTheory.Coalgebra.Quotient`, and tensor coalgebra data
in `Mathlib.RingTheory.Coalgebra.TensorProduct`. The comultiplication calculation
uses the shuffle naturality lemma `TensorProduct.tensorTensorTensorComm_comp_map`.
The weak bundled equivalence and its inverse come from
`Mathlib.RingTheory.Coalgebra.Equiv`; unique factorization reuses the quotient
lift and uniqueness API in `AlgebraicGroups.Algebra.Coalgebra.Quotient`.
-/

@[expose] public section

universe uR uC uD

open Coalgebra

namespace TensorProduct

variable {R : Type uR} [CommRing R]
variable {C : Type uC} [AddCommGroup C] [Module R C] [CoalgebraStruct R C]
variable {D : Type uD} [AddCommGroup D] [Module R D] [CoalgebraStruct R D]

private theorem map_mkQ_comul_comp (p : Submodule R C) (q : Submodule R D)
    [p.IsCoideal] [q.IsCoideal] :
    map (map p.mkQ q.mkQ) (map p.mkQ q.mkQ) ∘ₗ
        (comul (R := R) : C ⊗[R] D →ₗ[R] (C ⊗[R] D) ⊗[R] (C ⊗[R] D)) =
      (comul (R := R) : (C ⧸ p) ⊗[R] (D ⧸ q) →ₗ[R]
        ((C ⧸ p) ⊗[R] (D ⧸ q)) ⊗[R] ((C ⧸ p) ⊗[R] (D ⧸ q))) ∘ₗ
          map p.mkQ q.mkQ := by
  apply TensorProduct.ext'
  intro x y
  change map (map p.mkQ q.mkQ) (map p.mkQ q.mkQ)
      (tensorTensorTensorComm R C C D D (comul x ⊗ₜ[R] comul y)) =
    tensorTensorTensorComm R (C ⧸ p) (C ⧸ p) (D ⧸ q) (D ⧸ q)
      (map p.mkQ p.mkQ (comul x) ⊗ₜ[R] map q.mkQ q.mkQ (comul y))
  exact (LinearMap.congr_fun
    (tensorTensorTensorComm_comp_map R p.mkQ p.mkQ q.mkQ q.mkQ)
    (comul x ⊗ₜ[R] comul y)).symm

/-- The sum of the images of `p ⊗[R] D` and `C ⊗[R] q` is a coideal when
`p` and `q` are coideals. This is the relation submodule in Mathlib's
`TensorProduct.quotientTensorQuotientEquiv`; no flatness assumptions or coalgebra
laws are required. -/
theorem quotientTensorQuotient_isCoideal (p : Submodule R C) (q : Submodule R D)
    [p.IsCoideal] [q.IsCoideal] :
    (LinearMap.range (map p.subtype (LinearMap.id : D →ₗ[R] D)) ⊔
      LinearMap.range (map (LinearMap.id : C →ₗ[R] C) q.subtype)).IsCoideal := by
  let I : Submodule R (C ⊗[R] D) :=
    LinearMap.range (map p.subtype (LinearMap.id : D →ₗ[R] D)) ⊔
      LinearMap.range (map (LinearMap.id : C →ₗ[R] C) q.subtype)
  let π : C ⊗[R] D →ₗ[R] (C ⧸ p) ⊗[R] (D ⧸ q) := map p.mkQ q.mkQ
  let e := quotientTensorQuotientEquiv p q
  -- This comparison is entirely linear: the quotient by I has no coalgebra data yet.
  have he : e.toLinearMap ∘ₗ π = I.mkQ := by
    apply TensorProduct.ext'
    intro x y
    rfl
  have hπ (x : C ⊗[R] D) (hx : x ∈ I) : π x = 0 := by
    apply e.injective
    change (e.toLinearMap ∘ₗ π) x = e 0
    rw [he, map_zero]
    exact (Submodule.Quotient.mk_eq_zero I).2 hx
  have hcounit :
      (counit (R := R) : (C ⧸ p) ⊗[R] (D ⧸ q) →ₗ[R] R) ∘ₗ π =
        (counit (R := R) : C ⊗[R] D →ₗ[R] R) := by
    apply TensorProduct.ext'
    intro x y
    rfl
  change I.IsCoideal
  constructor
  · intro x hx
    calc
      counit (R := R) x = counit (R := R) (π x) :=
        (LinearMap.congr_fun hcounit x).symm
      _ = 0 := by rw [hπ x hx, map_zero]
  · intro x hx
    change map I.mkQ I.mkQ (comul x) = 0
    calc
      map I.mkQ I.mkQ (comul x) =
          map e.toLinearMap e.toLinearMap (map π π (comul x)) := by
        rw [map_map, he]
      _ = map e.toLinearMap e.toLinearMap (comul (π x)) := by
        exact congrArg (map e.toLinearMap e.toLinearMap)
          (LinearMap.congr_fun (map_mkQ_comul_comp p q) x)
      _ = 0 := by rw [hπ x hx, map_zero, map_zero]

section

attribute [local instance] quotientTensorQuotient_isCoideal

variable (p : Submodule R C) (q : Submodule R D) [p.IsCoideal] [q.IsCoideal]

local notation "Σ" =>
  (LinearMap.range (map p.subtype (LinearMap.id : D →ₗ[R] D)) ⊔
    LinearMap.range (map (LinearMap.id : C →ₗ[R] C) q.subtype))

/-- The tensor product of two coalgebra quotients is the quotient by the sum of
its two tensor relation images. The underlying linear equivalence is Mathlib's
`TensorProduct.quotientTensorQuotientEquiv`, and both endpoints use their canonical
coalgebra structures. Only comultiplication and counit data are required. -/
noncomputable def quotientTensorQuotientCoalgEquiv :
    (C ⧸ p) ⊗[R] (D ⧸ q) ≃ₗc[R] (C ⊗[R] D) ⧸ Σ := by
  let e := quotientTensorQuotientEquiv p q
  have he : e.toLinearMap.comp (map p.mkQ q.mkQ) = (Σ).mkQ := by
    apply TensorProduct.ext'
    intro x y
    rfl
  exact
    { e with
      counit_comp := by
        apply TensorProduct.ext'
        intro x y
        obtain ⟨x, rfl⟩ := p.mkQ_surjective x
        obtain ⟨y, rfl⟩ := q.mkQ_surjective y
        rfl
      map_comp_comul := by
        apply TensorProduct.ext'
        intro x y
        obtain ⟨x, rfl⟩ := p.mkQ_surjective x
        obtain ⟨y, rfl⟩ := q.mkQ_surjective y
        change map e.toLinearMap e.toLinearMap
            (comul (map p.mkQ q.mkQ (x ⊗ₜ[R] y))) =
          map (Σ).mkQ (Σ).mkQ (comul (x ⊗ₜ[R] y))
        calc
          map e.toLinearMap e.toLinearMap
              (comul (map p.mkQ q.mkQ (x ⊗ₜ[R] y))) =
              map e.toLinearMap e.toLinearMap
                (map (map p.mkQ q.mkQ) (map p.mkQ q.mkQ) (comul (x ⊗ₜ[R] y))) :=
            congrArg (map e.toLinearMap e.toLinearMap)
              (LinearMap.congr_fun (map_mkQ_comul_comp p q) (x ⊗ₜ[R] y)).symm
          _ = map (Σ).mkQ (Σ).mkQ (comul (x ⊗ₜ[R] y)) := by
            rw [map_map, he] }

/-- The coalgebra equivalence retains Mathlib's linear equivalence definitionally. -/
@[simp]
theorem quotientTensorQuotientCoalgEquiv_toLinearEquiv :
    (quotientTensorQuotientCoalgEquiv p q).toLinearEquiv =
      quotientTensorQuotientEquiv p q :=
  rfl

/-- The equivalence sends a tensor of quotient representatives to the tensor class. -/
@[simp]
theorem quotientTensorQuotientCoalgEquiv_apply_tmul_mk_tmul_mk (x : C) (y : D) :
    quotientTensorQuotientCoalgEquiv p q
        (Submodule.Quotient.mk (p := p) x ⊗ₜ[R] Submodule.Quotient.mk (p := q) y) =
      Submodule.Quotient.mk (p := Σ) (x ⊗ₜ[R] y) :=
  rfl

/-- The inverse sends a pure-tensor class to the tensor of the two quotient classes. -/
@[simp]
theorem quotientTensorQuotientCoalgEquiv_symm_apply_mk_tmul (x : C) (y : D) :
    (quotientTensorQuotientCoalgEquiv p q).symm
        (Submodule.Quotient.mk (p := Σ) (x ⊗ₜ[R] y)) =
      Submodule.Quotient.mk (p := p) x ⊗ₜ[R] Submodule.Quotient.mk (p := q) y :=
  rfl

/-- The canonical tensor quotient square commutes as an equality of linear maps. -/
theorem quotientTensorQuotientCoalgEquiv_comp_map_mkQ :
    (quotientTensorQuotientCoalgEquiv p q).toLinearEquiv.toLinearMap.comp
        (map p.mkQ q.mkQ) = (Σ).mkQ := by
  apply TensorProduct.ext'
  intro x y
  rfl

/-- Composing the inverse equivalence with the bundled quotient projection has
underlying linear map equal to the tensor product of the factor projections. -/
theorem quotientTensorQuotientCoalgEquiv_symm_comp_mkQCoalgHom_toLinearMap :
    ((quotientTensorQuotientCoalgEquiv p q).symm.toCoalgHom.comp
        (Coalgebra.Quotient.mkQCoalgHom Σ)).toLinearMap = map p.mkQ q.mkQ := by
  apply TensorProduct.ext'
  intro x y
  rfl

universe uE

variable {E : Type uE} [AddCommGroup E] [Module R E] [CoalgebraStruct R E]

/-- A coalgebra map vanishing on the two tensor relation images factors uniquely
through the tensor product of the quotients. The factor is the existing coideal
quotient lift composed with the canonical coalgebra equivalence. -/
theorem quotientTensorQuotientCoalgEquiv_existsUnique_factor
    (f : C ⊗[R] D →ₗc[R] E) (hf : Σ ≤ LinearMap.ker f.toLinearMap) :
    ∃! g : (C ⧸ p) ⊗[R] (D ⧸ q) →ₗc[R] E,
      g.toLinearMap.comp (map p.mkQ q.mkQ) = f.toLinearMap := by
  let e := quotientTensorQuotientCoalgEquiv p q
  refine ⟨((Σ).liftQCoalgHom f hf).comp e.toCoalgHom, ?_, ?_⟩
  · change (((Σ).liftQCoalgHom f hf).toLinearMap.comp e.toLinearEquiv.toLinearMap).comp
        (map p.mkQ q.mkQ) = f.toLinearMap
    rw [LinearMap.comp_assoc, quotientTensorQuotientCoalgEquiv_comp_map_mkQ p q]
    exact (Σ).liftQ_mkQ f.toLinearMap hf
  · intro g hg
    have hquot : (g.comp e.symm.toCoalgHom).comp
        (Coalgebra.Quotient.mkQCoalgHom Σ) = f := by
      apply CoalgHom.ext
      intro x
      change g (e.symm ((Σ).mkQ x)) = f x
      have hπ : e.symm ((Σ).mkQ x) = map p.mkQ q.mkQ x :=
        LinearMap.congr_fun
          (quotientTensorQuotientCoalgEquiv_symm_comp_mkQCoalgHom_toLinearMap p q) x
      rw [hπ]
      exact LinearMap.congr_fun hg x
    have hu : g.comp e.symm.toCoalgHom = (Σ).liftQCoalgHom f hf :=
      (Σ).liftQCoalgHom_unique f hf _ hquot
    apply CoalgHom.ext
    intro z
    calc
      g z = (g.comp e.symm.toCoalgHom) (e z) := by
        change g z = g (e.symm (e z))
        rw [CoalgEquiv.symm_apply_apply]
      _ = ((Σ).liftQCoalgHom f hf) (e z) := CoalgHom.congr_fun hu (e z)
      _ = (((Σ).liftQCoalgHom f hf).comp e.toCoalgHom) z := rfl

end

end TensorProduct
