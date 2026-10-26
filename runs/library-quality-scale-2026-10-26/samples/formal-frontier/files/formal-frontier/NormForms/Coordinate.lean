/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.Norm.Basic

/-!
# Coordinate norm forms

This module constructs the field norm as a homogeneous multivariable polynomial in the
coordinates supplied by a finite basis.  It also records its behavior under an arbitrary
change of basis and under a reindexing of the basis.

The norm form is the signed constant coefficient of the characteristic polynomial
of multiplication, with the finite free-module instances derived from the basis.
`coordinateChange b b'` maps the new `b'`-coordinates into the old `b`-coordinates.
The change-of-basis polynomial law uses structural substitution (`bind₁`), not
equality of evaluations, so it also applies over finite fields. The four public
definition bodies are exposed to retain explicit unfolding for downstream clients;
the matrix and characteristic-polynomial comparison proofs remain private.
-/

set_option warningAsError true

universe u v w w'

namespace NormForms

public section

open Module MvPolynomial

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ι : Type w} {κ : Type w'} [Fintype ι] [Fintype κ]

/-- The field norm in the coordinates supplied by a finite basis. -/
@[expose]
noncomputable def coordinateNorm (b : Basis ι K L) (x : ι → K) : K :=
  Algebra.norm K (b.equivFun.symm x)

/-- A coordinate norm vanishes exactly at the zero coordinate vector. -/
theorem coordinateNorm_eq_zero_iff (b : Basis ι K L) (x : ι → K) :
    coordinateNorm b x = 0 ↔ x = 0 := by
  rw [coordinateNorm, Algebra.norm_eq_zero_iff_of_basis b]
  exact b.equivFun.symm.map_eq_zero_iff

/-- The coordinate norm is homogeneous under scalar multiplication. -/
theorem coordinateNorm_smul (b : Basis ι K L) (a : K) (x : ι → K) :
    coordinateNorm b (a • x) = a ^ Fintype.card ι * coordinateNorm b x := by
  rw [coordinateNorm, coordinateNorm, map_smul, Algebra.smul_def, map_mul,
    Algebra.norm_algebraMap_of_basis b]

/-- Convert coordinates in `b'` to coordinates in `b`. -/
@[expose]
noncomputable def coordinateChange (b : Basis ι K L) (b' : Basis κ K L) :
    (κ → K) ≃ₗ[K] (ι → K) :=
  b'.equivFun.symm.trans b.equivFun

/-- Converting coordinates does not change the represented element. -/
@[simp]
theorem coordinateChange_apply (b : Basis ι K L) (b' : Basis κ K L) (x : κ → K) :
    coordinateChange b b' x = b.equivFun (b'.equivFun.symm x) :=
  rfl

/-- The coordinate norm is independent of the chosen coordinates. -/
@[simp↓]
theorem coordinateNorm_coordinateChange (b : Basis ι K L) (b' : Basis κ K L)
    (x : κ → K) :
    coordinateNorm b (coordinateChange b b' x) = coordinateNorm b' x := by
  simp [coordinateNorm, coordinateChange]

/-- The signed constant characteristic coefficient giving the coordinate norm form. -/
@[expose]
noncomputable def coordinateNormPolynomial (b : Basis ι K L) : MvPolynomial ι K := by
  classical
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  exact C ((-1 : K) ^ Module.finrank K L) *
    (LinearMap.polyCharpoly (Algebra.lmul K L).toLinearMap b).coeff 0

/-- The coordinate norm polynomial is homogeneous of degree equal to the basis cardinality. -/
theorem coordinateNormPolynomial_isHomogeneous (b : Basis ι K L) :
    (coordinateNormPolynomial b).IsHomogeneous (Fintype.card ι) := by
  classical
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  rw [coordinateNormPolynomial]
  apply MvPolynomial.IsHomogeneous.C_mul
  apply LinearMap.polyCharpoly_coeff_isHomogeneous
  simp [Module.finrank_eq_card_basis b]

/-- Evaluation of the coordinate norm polynomial is the field norm in those coordinates. -/
theorem coordinateNormPolynomial_eval (b : Basis ι K L) (x : ι → K) :
    MvPolynomial.eval x (coordinateNormPolynomial b) = coordinateNorm b x := by
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  classical
  rw [coordinateNormPolynomial, map_mul, eval_C]
  have hx : (b.repr (b.equivFun.symm x) : ι → K) = x := by
    change b.equivFun (b.equivFun.symm x) = x
    exact b.equivFun.apply_symm_apply x
  nth_rewrite 1 [← hx]
  rw [LinearMap.polyCharpoly_coeff_eval]
  rw [← LinearMap.det_eq_sign_charpoly_coeff]
  rfl

/-- The coordinate norm polynomial has no nontrivial zero. -/
theorem coordinateNormPolynomial_eval_eq_zero_iff (b : Basis ι K L) (x : ι → K) :
    MvPolynomial.eval x (coordinateNormPolynomial b) = 0 ↔ x = 0 := by
  rw [coordinateNormPolynomial_eval, coordinateNorm_eq_zero_iff]

/-- A coordinate norm polynomial is nonzero. -/
theorem coordinateNormPolynomial_ne_zero (b : Basis ι K L) :
    coordinateNormPolynomial b ≠ 0 := by
  intro h
  have hx : b.equivFun (1 : L) = 0 :=
    (coordinateNormPolynomial_eval_eq_zero_iff b (b.equivFun 1)).mp (by simp [h])
  have h1 : (1 : L) = 0 := b.equivFun.injective (by
    rw [map_zero]
    exact hx)
  exact one_ne_zero h1

/-- The exact total degree of a coordinate norm polynomial. -/
theorem coordinateNormPolynomial_totalDegree (b : Basis ι K L) :
    (coordinateNormPolynomial b).totalDegree = Fintype.card ι :=
  (coordinateNormPolynomial_isHomogeneous b).totalDegree
    (coordinateNormPolynomial_ne_zero b)

/-- Evaluation after a change of coordinates gives the norm in the new coordinates. -/
theorem coordinateNormPolynomial_eval_coordinateChange
    (b : Basis ι K L) (b' : Basis κ K L) (x : κ → K) :
    MvPolynomial.eval (coordinateChange b b' x) (coordinateNormPolynomial b) =
      MvPolynomial.eval x (coordinateNormPolynomial b') := by
  rw [coordinateNormPolynomial_eval, coordinateNorm_coordinateChange,
    coordinateNormPolynomial_eval]

/- The next three private lemmas expose the functoriality already implicit in
`LinearMap.polyCharpoly`; they avoid any evaluation-extensionality assumption on the field. -/

private theorem matrix_toMvPolynomial_submatrix_equiv
    {R m α β : Type*} [CommRing R]
    [Fintype α] [Fintype β] (M : Matrix m α R) (e : α ≃ β) (i : m) :
    Matrix.toMvPolynomial (M.submatrix id e.symm) i =
      MvPolynomial.rename e (Matrix.toMvPolynomial M i) := by
  classical
  simp only [Matrix.toMvPolynomial, Matrix.submatrix_apply, id_eq, map_sum,
    MvPolynomial.rename_monomial, Finsupp.mapDomain_single]
  rw [← Equiv.sum_comp e
    (fun j => MvPolynomial.monomial (Finsupp.single j 1) (M i (e.symm j)))]
  simp

private theorem linearMap_toMvPolynomial_reindex
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {α β γ : Type*}
    [Fintype α] [Fintype β] [Finite γ] [DecidableEq α] [DecidableEq β]
    (b : Basis α R M) (c : Basis γ R N) (e : α ≃ β)
    (f : M →ₗ[R] N) (i : γ) :
    LinearMap.toMvPolynomial (b.reindex e) c f i =
      MvPolynomial.rename e (LinearMap.toMvPolynomial b c f i) := by
  classical
  unfold LinearMap.toMvPolynomial
  rw [LinearMap.toMatrix_eq_basisToMatrix, LinearMap.toMatrix_eq_basisToMatrix]
  have h : c.toMatrix (⇑f ∘ ⇑(b.reindex e)) =
      (c.toMatrix (⇑f ∘ ⇑b)).submatrix id e.symm := by
    ext j k
    simp [Basis.toMatrix_apply]
  rw [h]
  exact matrix_toMvPolynomial_submatrix_equiv _ e i

private theorem polyCharpoly_reindex
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {α β γ : Type*}
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    [Module.Free R N] [Module.Finite R N]
    (b : Basis α R M) (c : Basis γ R N) (e : α ≃ β)
    (f : M →ₗ[R] Module.End R N) :
    LinearMap.polyCharpoly f (b.reindex e) =
      (LinearMap.polyCharpoly f b).map (MvPolynomial.rename e).toRingHom := by
  classical
  rcases subsingleton_or_nontrivial R with trivialRing | nontrivialRing
  · let _ : Subsingleton R := trivialRing
    exact Subsingleton.elim _ _
  · let _ : Nontrivial R := nontrivialRing
    let _ : Finite γ := Module.Finite.finite_basis c
    let _ : Fintype γ := Fintype.ofFinite γ
    rw [LinearMap.polyCharpoly_eq_of_basis f (b.reindex e) c,
      LinearMap.polyCharpoly_eq_of_basis f b c]
    rw [Polynomial.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        MvPolynomial.bind₁_X_right]
      rw [linearMap_toMvPolynomial_reindex]
      rfl

/-- Reindexing a basis renames the variables of its coordinate norm polynomial. -/
theorem coordinateNormPolynomial_reindex (b : Basis ι K L) (e : ι ≃ κ) :
    coordinateNormPolynomial (b.reindex e) =
      MvPolynomial.rename e (coordinateNormPolynomial b) := by
  classical
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  rw [coordinateNormPolynomial, coordinateNormPolynomial]
  have h := polyCharpoly_reindex b b e (Algebra.lmul K L).toLinearMap
  rw [h]
  simp only [Polynomial.coeff_map, map_mul, MvPolynomial.rename_C]
  rfl

/-- Reindexing coordinates acts by precomposition with the indexing equivalence. -/
theorem coordinateNorm_reindex (b : Basis ι K L) (e : ι ≃ κ) (x : κ → K) :
    coordinateNorm (b.reindex e) x = coordinateNorm b (x ∘ e) := by
  rw [← coordinateNormPolynomial_eval (b.reindex e),
    coordinateNormPolynomial_reindex, MvPolynomial.eval_rename,
    coordinateNormPolynomial_eval]

/-- The linear polynomials expressing `b`-coordinates in terms of `b'`-coordinates. -/
@[expose]
noncomputable def coordinateChangePolynomial
    (b : Basis ι K L) (b' : Basis κ K L) (i : ι) : MvPolynomial κ K := by
  classical
  exact LinearMap.id.toMvPolynomial b' b i

/-- The coordinate-change polynomials evaluate to the coordinate-change linear equivalence. -/
theorem coordinateChangePolynomial_eval
    (b : Basis ι K L) (b' : Basis κ K L) (x : κ → K) (i : ι) :
    MvPolynomial.eval x (coordinateChangePolynomial b b' i) =
      coordinateChange b b' x i := by
  classical
  let c : κ →₀ K := Finsupp.equivFunOnFinite.symm x
  have hc : (c : κ → K) = x := Finsupp.equivFunOnFinite.apply_symm_apply x
  rw [← hc, coordinateChangePolynomial, LinearMap.toMvPolynomial_eval_eq_apply]
  change b.equivFun (b'.equivFun.symm x) i = b.equivFun (b'.equivFun.symm x) i
  rfl

private theorem polyCharpoly_changeBasis
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {α β γ : Type*}
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    [Module.Free R N] [Module.Finite R N]
    (b : Basis α R M) (b' : Basis β R M) (c : Basis γ R N)
    (f : M →ₗ[R] Module.End R N) :
    LinearMap.polyCharpoly f b' =
      (LinearMap.polyCharpoly f b).map
        (MvPolynomial.bind₁ (LinearMap.id.toMvPolynomial b' b)).toRingHom := by
  classical
  rcases subsingleton_or_nontrivial R with trivialRing | nontrivialRing
  · let _ : Subsingleton R := trivialRing
    exact Subsingleton.elim _ _
  · let _ : Nontrivial R := nontrivialRing
    let _ : Finite γ := Module.Finite.finite_basis c
    let _ : Fintype γ := Fintype.ofFinite γ
    rw [LinearMap.polyCharpoly_eq_of_basis f b' c,
      LinearMap.polyCharpoly_eq_of_basis f b c]
    rw [Polynomial.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        MvPolynomial.bind₁_X_right]
      change LinearMap.toMvPolynomial b' c.end f i =
        MvPolynomial.bind₁ (LinearMap.id.toMvPolynomial b' b)
          (LinearMap.toMvPolynomial b c.end f i)
      rw [← LinearMap.toMvPolynomial_comp b' b c.end f LinearMap.id]
      rfl

/-- An arbitrary change of basis substitutes its coordinate linear forms into the norm form. -/
theorem coordinateNormPolynomial_changeBasis
    (b : Basis ι K L) (b' : Basis κ K L) :
    coordinateNormPolynomial b' =
      MvPolynomial.bind₁ (coordinateChangePolynomial b b')
        (coordinateNormPolynomial b) := by
  classical
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  rw [coordinateNormPolynomial, coordinateNormPolynomial]
  have h := polyCharpoly_changeBasis b b' b (Algebra.lmul K L).toLinearMap
  rw [h]
  unfold coordinateChangePolynomial
  simp only [Polynomial.coeff_map, map_mul, MvPolynomial.bind₁_C_right]
  rfl

end

end NormForms
