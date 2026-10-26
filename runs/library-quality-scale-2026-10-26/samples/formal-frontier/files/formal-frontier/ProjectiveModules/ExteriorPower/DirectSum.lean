/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior powers of a direct sum

This file gives the fixed-degree decomposition of the exterior power of a binary direct sum.
It is valid for arbitrary modules over an arbitrary commutative ring, including degree zero.
-/

@[expose] public section

noncomputable section

open scoped DirectSum TensorProduct

namespace exteriorPower

universe u v w

variable (R : Type u) [CommRing R]
variable (P : Type v) (Q : Type w)
variable [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

private abbrev Bidegree (ij : ℕ × ℕ) :=
  (⋀[R]^ij.1 P) ⊗[R] (⋀[R]^ij.2 Q)

/-- The ambient decomposition of the full exterior algebra into all pairs of degrees. -/
private noncomputable def ambientDirectSumEquiv :
    ExteriorAlgebra R (P × Q) ≃ₗ[R] ⨁ ij : ℕ × ℕ, Bidegree R P Q ij :=
  (ExteriorAlgebra.prodEquivTensor R P Q).toLinearEquiv ≪≫ₗ
    GradedTensorProduct.auxEquiv R
      (fun i : ℕ ↦ ⋀[R]^i P) (fun j : ℕ ↦ ⋀[R]^j Q) ≪≫ₗ
    TensorProduct.directSum R R
      (fun i : ℕ ↦ ⋀[R]^i P) (fun j : ℕ ↦ ⋀[R]^j Q)

private theorem ambientDirectSumEquiv_symm_of_tmul (i j : ℕ)
    (p : Fin i → P) (q : Fin j → Q) :
    (ambientDirectSumEquiv R P Q).symm
        (DirectSum.of (Bidegree R P Q) (i, j)
          (exteriorPower.ιMulti R i p ⊗ₜ[R] exteriorPower.ιMulti R j q)) =
      ExteriorAlgebra.ιMulti R (i + j)
        (Fin.append (LinearMap.inl R P Q ∘ p) (LinearMap.inr R P Q ∘ q)) := by
  rw [ambientDirectSumEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_symm]
  simp only [LinearEquiv.trans_apply]
  rw [← DirectSum.lof_eq_of R]
  rw [TensorProduct.directSum_symm_lof_tmul]
  have haux :
      (GradedTensorProduct.auxEquiv R
        (fun a : ℕ ↦ ⋀[R]^a P) (fun b : ℕ ↦ ⋀[R]^b Q)).symm
          (DirectSum.lof R ℕ (fun a : ℕ ↦ ⋀[R]^a P) i
              (exteriorPower.ιMulti R i p) ⊗ₜ[R]
            DirectSum.lof R ℕ (fun b : ℕ ↦ ⋀[R]^b Q) j
              (exteriorPower.ιMulti R j q)) =
        ((exteriorPower.ιMulti R i p : ExteriorAlgebra R P) ᵍ⊗ₜ[R]
          (exteriorPower.ιMulti R j q : ExteriorAlgebra R Q)) := by
    rw [LinearEquiv.symm_apply_eq, GradedTensorProduct.auxEquiv_tmul]
    simp only [DirectSum.decompose_coe, DirectSum.lof_eq_of]
  rw [haux]
  exact ExteriorAlgebra.prodEquivTensor_symm_apply_tmul_ιMulti R P Q i j p q

private theorem ambientDirectSumEquiv_symm_of_tmul' (i j : ℕ)
    (a : ⋀[R]^i P) (b : ⋀[R]^j Q) :
    (ambientDirectSumEquiv R P Q).symm
        (DirectSum.of (Bidegree R P Q) (i, j) (a ⊗ₜ[R] b)) =
      ExteriorAlgebra.map (LinearMap.inl R P Q) a.1 *
        ExteriorAlgebra.map (LinearMap.inr R P Q) b.1 := by
  rw [ambientDirectSumEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_symm]
  simp only [LinearEquiv.trans_apply]
  rw [← DirectSum.lof_eq_of R]
  rw [TensorProduct.directSum_symm_lof_tmul]
  have haux :
      (GradedTensorProduct.auxEquiv R
        (fun d : ℕ ↦ ⋀[R]^d P) (fun d : ℕ ↦ ⋀[R]^d Q)).symm
          (DirectSum.lof R ℕ (fun d : ℕ ↦ ⋀[R]^d P) i a ⊗ₜ[R]
            DirectSum.lof R ℕ (fun d : ℕ ↦ ⋀[R]^d Q) j b) =
        ((a.1 : ExteriorAlgebra R P) ᵍ⊗ₜ[R] (b.1 : ExteriorAlgebra R Q)) := by
    rw [LinearEquiv.symm_apply_eq, GradedTensorProduct.auxEquiv_tmul]
    simp only [DirectSum.decompose_coe, DirectSum.lof_eq_of]
  rw [haux]
  exact ExteriorAlgebra.prodEquivTensor_symm_tmul R P Q a.1 b.1

private theorem ambientDirectSumEquiv_symm_of_mem (i j : ℕ)
    (z : (⋀[R]^i P) ⊗[R] (⋀[R]^j Q)) :
    (ambientDirectSumEquiv R P Q).symm
        (DirectSum.of (Bidegree R P Q) (i, j) z) ∈ ⋀[R]^(i + j) (P × Q) := by
  let L : ((⋀[R]^i P) ⊗[R] (⋀[R]^j Q)) →ₗ[R] ExteriorAlgebra R (P × Q) :=
    (ambientDirectSumEquiv R P Q).symm.toLinearMap.comp
      (DirectSum.lof R (ℕ × ℕ) (Bidegree R P Q) (i, j))
  change L z ∈ ⋀[R]^(i + j) (P × Q)
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa using add_mem hx hy
  | tmul x y =>
      have hx : x ∈ (⊤ : Submodule R (⋀[R]^i P)) := Submodule.mem_top
      have hy : y ∈ (⊤ : Submodule R (⋀[R]^j Q)) := Submodule.mem_top
      rw [← exteriorPower.ιMulti_span R i P] at hx
      rw [← exteriorPower.ιMulti_span R j Q] at hy
      refine Submodule.span_induction₂
        (p := fun a b _ _ ↦ L (a ⊗ₜ[R] b) ∈ ⋀[R]^(i + j) (P × Q))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro a b ⟨p, rfl⟩ ⟨q, rfl⟩
        change (ambientDirectSumEquiv R P Q).symm
          (DirectSum.of (Bidegree R P Q) (i, j)
            (exteriorPower.ιMulti R i p ⊗ₜ[R] exteriorPower.ιMulti R j q)) ∈
              ⋀[R]^(i + j) (P × Q)
        rw [ambientDirectSumEquiv_symm_of_tmul]
        exact (exteriorPower.ιMulti R (i + j)
          (Fin.append (LinearMap.inl R P Q ∘ p) (LinearMap.inr R P Q ∘ q))).2
      · simp
      · simp
      · intro a a' b _ _ _ h h'
        rw [TensorProduct.add_tmul, map_add]
        exact add_mem h h'
      · intro a b b' _ _ _ h h'
        rw [TensorProduct.tmul_add, map_add]
        exact add_mem h h'
      · intro r a b _ _ h
        rw [← TensorProduct.smul_tmul', map_smul]
        exact Submodule.smul_mem _ _ h
      · intro r a b _ _ h
        rw [TensorProduct.tmul_smul, map_smul]
        exact Submodule.smul_mem _ _ h

/-- Keep only the bidegrees whose total degree is `n`. -/
private noncomputable def totalDegreeComponent (n : ℕ) :
    (⨁ ij : ℕ × ℕ, Bidegree R P Q ij) →ₗ[R]
      ⨁ ij : ℕ × ℕ, Bidegree R P Q ij :=
  DirectSum.lmap fun ij ↦
    if ij.1 + ij.2 = n then LinearMap.id else 0

private theorem totalDegreeComponent_of (n : ℕ) (ij : ℕ × ℕ)
    (z : Bidegree R P Q ij) :
    totalDegreeComponent R P Q n (DirectSum.of (Bidegree R P Q) ij z) =
      if ij.1 + ij.2 = n then DirectSum.of (Bidegree R P Q) ij z else 0 := by
  classical
  by_cases h : ij.1 + ij.2 = n <;> simp [totalDegreeComponent, h]

/-- Exterior homogeneous projection corresponds to retaining all bidegrees of the same total
degree in the ambient direct-sum decomposition. -/
private theorem proj_ambientDirectSumEquiv_symm (n : ℕ)
    (y : ⨁ ij : ℕ × ℕ, Bidegree R P Q ij) :
    GradedAlgebra.proj (fun d : ℕ ↦ ⋀[R]^d (P × Q)) n
        ((ambientDirectSumEquiv R P Q).symm y) =
      (ambientDirectSumEquiv R P Q).symm (totalDegreeComponent R P Q n y) := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | of ij z =>
      by_cases h : ij.1 + ij.2 = n
      · simp only [totalDegreeComponent_of, h]
        rw [GradedAlgebra.proj_apply]
        exact DirectSum.decompose_of_mem_same
          (fun d : ℕ ↦ ⋀[R]^d (P × Q))
          (h ▸ ambientDirectSumEquiv_symm_of_mem R P Q ij.1 ij.2 z)
      · simp only [totalDegreeComponent_of, h]
        rw [GradedAlgebra.proj_apply]
        exact DirectSum.decompose_of_mem_ne
          (fun d : ℕ ↦ ⋀[R]^d (P × Q))
          (ambientDirectSumEquiv_symm_of_mem R P Q ij.1 ij.2 z) h

/-- An element of exterior degree `k` has no ambient component in a bidegree of different total
degree. -/
private theorem ambientDirectSumEquiv_apply_eq_zero {k : ℕ}
    (x : ⋀[R]^k (P × Q)) (ij : ℕ × ℕ) (hij : ij.1 + ij.2 ≠ k) :
    ambientDirectSumEquiv R P Q x.1 ij = 0 := by
  classical
  let y := ambientDirectSumEquiv R P Q x.1
  have hproj :
      GradedAlgebra.proj (fun d : ℕ ↦ ⋀[R]^d (P × Q)) (ij.1 + ij.2) x.1 = 0 := by
    rw [GradedAlgebra.proj_apply]
    exact DirectSum.decompose_of_mem_ne
      (fun d : ℕ ↦ ⋀[R]^d (P × Q)) x.2 hij.symm
  have hcomponent : totalDegreeComponent R P Q (ij.1 + ij.2) y = 0 := by
    apply (ambientDirectSumEquiv R P Q).symm.injective
    rw [map_zero, ← proj_ambientDirectSumEquiv_symm]
    simpa [y] using hproj
  have hc := DFunLike.congr_fun hcomponent ij
  change (if ij.1 + ij.2 = ij.1 + ij.2 then LinearMap.id else 0) (y ij) = 0 at hc
  simpa [y] using hc

private abbrev Antidiagonal (k : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 = k}

private abbrev AntidiagonalBidegree (k : ℕ) (a : Antidiagonal k) :=
  Bidegree R P Q a.1

/-- Include the direct sum over one antidiagonal into the ambient bidegree direct sum. -/
private noncomputable def antidiagonalIncl (k : ℕ) :
    (⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a) →ₗ[R]
      ⨁ ij : ℕ × ℕ, Bidegree R P Q ij :=
  DirectSum.toModule R _ _ fun a ↦
    DirectSum.lof R (ℕ × ℕ) (Bidegree R P Q) a.1

/-- Restrict the ambient bidegree direct sum to one antidiagonal. -/
private noncomputable def antidiagonalProj (k : ℕ) :
    (⨁ ij : ℕ × ℕ, Bidegree R P Q ij) →ₗ[R]
      ⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a :=
  DirectSum.toModule R _ _ fun ij ↦
    if h : ij.1 + ij.2 = k then
      DirectSum.lof R (Antidiagonal k) (AntidiagonalBidegree R P Q k) ⟨ij, h⟩
    else 0

private theorem antidiagonalProj_incl (k : ℕ) :
    (antidiagonalProj R P Q k).comp (antidiagonalIncl R P Q k) = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro a
  apply LinearMap.ext
  intro z
  simp [antidiagonalIncl, antidiagonalProj, a.2]

private theorem antidiagonalIncl_proj_component (k : ℕ)
    (y : ⨁ ij : ℕ × ℕ, Bidegree R P Q ij) (ij : ℕ × ℕ) :
    antidiagonalIncl R P Q k (antidiagonalProj R P Q k y) ij =
      if ij.1 + ij.2 = k then y ij else 0 := by
  classical
  let lhs : (⨁ ab : ℕ × ℕ, Bidegree R P Q ab) →ₗ[R] Bidegree R P Q ij :=
    (DirectSum.component R (ℕ × ℕ) (Bidegree R P Q) ij).comp
      ((antidiagonalIncl R P Q k).comp (antidiagonalProj R P Q k))
  let rhs : (⨁ ab : ℕ × ℕ, Bidegree R P Q ab) →ₗ[R] Bidegree R P Q ij :=
    if ij.1 + ij.2 = k then
      DirectSum.component R (ℕ × ℕ) (Bidegree R P Q) ij
    else 0
  have heq : lhs = rhs := by
    apply DirectSum.linearMap_ext
    intro ab
    apply LinearMap.ext
    intro z
    by_cases hab : ab.1 + ab.2 = k
    · by_cases h : ab = ij
      · subst ab
        simp [lhs, rhs, antidiagonalIncl, antidiagonalProj, hab]
      · by_cases hij : ij.1 + ij.2 = k <;>
          simp [lhs, rhs, antidiagonalIncl, antidiagonalProj, hab,
            DirectSum.component.of, h, hij]
    · by_cases h : ab = ij
      · subst ab
        simp [lhs, rhs, antidiagonalIncl, antidiagonalProj, hab]
      · by_cases hij : ij.1 + ij.2 = k <;>
          simp [lhs, rhs, antidiagonalIncl, antidiagonalProj, hab,
            DirectSum.component.of, h, hij]
  change (DirectSum.component R (ℕ × ℕ) (Bidegree R P Q) ij)
    (antidiagonalIncl R P Q k (antidiagonalProj R P Q k y)) =
      if ij.1 + ij.2 = k then
        DirectSum.component R (ℕ × ℕ) (Bidegree R P Q) ij y else 0
  have hfun := LinearMap.congr_fun heq y
  by_cases hij : ij.1 + ij.2 = k <;> simpa [lhs, rhs, hij] using hfun

private theorem antidiagonalIncl_proj_eq_of_support (k : ℕ)
    (y : ⨁ ij : ℕ × ℕ, Bidegree R P Q ij)
    (hy : ∀ ij, ij.1 + ij.2 ≠ k → y ij = 0) :
    antidiagonalIncl R P Q k (antidiagonalProj R P Q k y) = y := by
  classical
  apply DirectSum.ext
  intro ij
  rw [antidiagonalIncl_proj_component]
  by_cases h : ij.1 + ij.2 = k
  · simp [h]
  · simp [h, hy ij h]

private theorem ambientDirectSumEquiv_symm_antidiagonalIncl_mem (k : ℕ)
    (z : ⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a) :
    (ambientDirectSumEquiv R P Q).symm (antidiagonalIncl R P Q k z) ∈
      ⋀[R]^k (P × Q) := by
  classical
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa using add_mem hx hy
  | of a z =>
      rw [← DirectSum.lof_eq_of R]
      simp only [antidiagonalIncl, DirectSum.toModule_lof]
      have hm := ambientDirectSumEquiv_symm_of_mem R P Q a.1.1 a.1.2 z
      rw [a.2] at hm
      exact hm

private noncomputable def fixedDegreeForward (k : ℕ) :
    (⋀[R]^k (P × Q)) →ₗ[R]
      ⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a :=
  (antidiagonalProj R P Q k).comp
    ((ambientDirectSumEquiv R P Q).toLinearMap.comp (⋀[R]^k (P × Q)).subtype)

private noncomputable def fixedDegreeInverse (k : ℕ) :
    (⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a) →ₗ[R]
      ⋀[R]^k (P × Q) :=
  ((ambientDirectSumEquiv R P Q).symm.toLinearMap.comp
    (antidiagonalIncl R P Q k)).codRestrict (⋀[R]^k (P × Q))
      (ambientDirectSumEquiv_symm_antidiagonalIncl_mem R P Q k)

/-- The fixed-degree part of the ambient exterior-algebra decomposition, indexed by pairs whose
sum is the chosen degree. -/
private noncomputable def fixedDegreeAntidiagonalEquiv (k : ℕ) :
    (⋀[R]^k (P × Q)) ≃ₗ[R]
      ⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a :=
  LinearEquiv.ofLinearMap (fixedDegreeForward R P Q k) (fixedDegreeInverse R P Q k)
    (by
      apply LinearMap.ext
      intro z
      dsimp [fixedDegreeForward, fixedDegreeInverse]
      change antidiagonalProj R P Q k
        (ambientDirectSumEquiv R P Q
          ((ambientDirectSumEquiv R P Q).symm (antidiagonalIncl R P Q k z))) = z
      rw [LinearEquiv.apply_symm_apply]
      exact LinearMap.congr_fun (antidiagonalProj_incl R P Q k) z)
    (by
      apply LinearMap.ext
      intro x
      dsimp [fixedDegreeForward, fixedDegreeInverse]
      apply Subtype.ext
      change (ambientDirectSumEquiv R P Q).symm
        (antidiagonalIncl R P Q k
          (antidiagonalProj R P Q k (ambientDirectSumEquiv R P Q x.1))) = x.1
      rw [antidiagonalIncl_proj_eq_of_support R P Q k _
        (fun ij hij ↦ ambientDirectSumEquiv_apply_eq_zero R P Q x ij hij)]
      exact (ambientDirectSumEquiv R P Q).symm_apply_apply x.1)

private theorem coe_fixedDegreeAntidiagonalEquiv_symm_of (k : ℕ)
    (a : Antidiagonal k) (z : AntidiagonalBidegree R P Q k a) :
    ((fixedDegreeAntidiagonalEquiv R P Q k).symm
        (DirectSum.of (AntidiagonalBidegree R P Q k) a z) : ExteriorAlgebra R (P × Q)) =
      (ambientDirectSumEquiv R P Q).symm
        (DirectSum.of (Bidegree R P Q) a.1 z) := by
  rw [fixedDegreeAntidiagonalEquiv]
  change (ambientDirectSumEquiv R P Q).symm
    (antidiagonalIncl R P Q k (DirectSum.of (AntidiagonalBidegree R P Q k) a z)) = _
  congr 1
  change (DirectSum.toModule R (Antidiagonal k)
      (⨁ ij : ℕ × ℕ, Bidegree R P Q ij)
      (fun a ↦ DirectSum.lof R (ℕ × ℕ) (Bidegree R P Q) a.1))
        (DirectSum.lof R (Antidiagonal k) (AntidiagonalBidegree R P Q k) a z) =
      DirectSum.lof R (ℕ × ℕ) (Bidegree R P Q) a.1 z
  rw [DirectSum.toModule_lof]

/-- The natural bijection between `Fin (k + 1)` and pairs of natural numbers with sum `k`. -/
private abbrev finEquivAntidiagonal (k : ℕ) : Fin (k + 1) ≃ Antidiagonal k where
  toFun i := ⟨(i, k - i), Nat.add_sub_of_le (Nat.lt_succ_iff.mp i.2)⟩
  invFun a := ⟨a.1.1, by omega⟩
  left_inv i := Fin.ext rfl
  right_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change k - a.1.1 = a.1.2
      omega

private noncomputable def antidiagonalFinEquiv (k : ℕ) :
    (⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a) ≃ₗ[R]
      ⨁ i : Fin (k + 1), (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(k - i.1) Q) :=
  DirectSum.lequivCongrLeft R (finEquivAntidiagonal k).symm

private theorem antidiagonalFinEquiv_symm_of (k : ℕ) (i : Fin (k + 1))
    (z : (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(k - i.1) Q)) :
    (antidiagonalFinEquiv R P Q k).symm
        (DirectSum.of
          (fun j : Fin (k + 1) ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(k - j.1) Q)) i z) =
      DirectSum.of (AntidiagonalBidegree R P Q k)
        ⟨(i.1, k - i.1), Nat.add_sub_of_le (Nat.lt_succ_iff.mp i.2)⟩ z := by
  rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R]
  rw [antidiagonalFinEquiv]
  convert (DirectSum.lequivCongrLeft_symm_lof
      (R := R) (M := AntidiagonalBidegree R P Q k)
      (h := (finEquivAntidiagonal k).symm) (k := i) (x := z)) using 1 <;>
    simp [finEquivAntidiagonal]

/-- The degree-`k` exterior power of a binary direct sum is the direct sum of the tensor products
of exterior powers whose degrees add to `k`.

The inverse uses the ordered convention: the `P` block is wedged before the `Q` block. No
finiteness, projectivity, flatness, or nontriviality assumption is needed. -/
@[no_expose]
noncomputable def prodEquivDirectSum (k : ℕ) :
    (⋀[R]^k (P × Q)) ≃ₗ[R]
      ⨁ i : Fin (k + 1), (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(k - i.1) Q) :=
  fixedDegreeAntidiagonalEquiv R P Q k ≪≫ₗ antidiagonalFinEquiv R P Q k

/-- The inverse of `prodEquivDirectSum` sends a pure tensor in the `i`th summand to exterior
multiplication after the two canonical inclusions, with the `P` factor first. -/
@[simp]
theorem coe_prodEquivDirectSum_symm_of_tmul (k : ℕ) (i : Fin (k + 1))
    (a : ⋀[R]^i.1 P) (b : ⋀[R]^(k - i.1) Q) :
    ((prodEquivDirectSum R P Q k).symm
        (DirectSum.of
          (fun j : Fin (k + 1) ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(k - j.1) Q)) i
          (a ⊗ₜ[R] b)) : ExteriorAlgebra R (P × Q)) =
      ExteriorAlgebra.map (LinearMap.inl R P Q) a.1 *
        ExteriorAlgebra.map (LinearMap.inr R P Q) b.1 := by
  rw [prodEquivDirectSum, LinearEquiv.trans_symm]
  simp only [LinearEquiv.trans_apply]
  rw [antidiagonalFinEquiv_symm_of]
  rw [coe_fixedDegreeAntidiagonalEquiv_symm_of]
  exact ambientDirectSumEquiv_symm_of_tmul' R P Q i.1 (k - i.1) a b

/-- On pure exterior products, the inverse concatenates the `P` entries and then the `Q`
entries. The right side is written in the full exterior algebra, avoiding any index casts. -/
theorem coe_prodEquivDirectSum_symm_of_tmul_ιMulti (k : ℕ) (i : Fin (k + 1))
    (p : Fin i.1 → P) (q : Fin (k - i.1) → Q) :
    ((prodEquivDirectSum R P Q k).symm
        (DirectSum.of
          (fun j : Fin (k + 1) ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(k - j.1) Q)) i
          (exteriorPower.ιMulti R i.1 p ⊗ₜ[R]
            exteriorPower.ιMulti R (k - i.1) q)) : ExteriorAlgebra R (P × Q)) =
      ExteriorAlgebra.ιMulti R (i.1 + (k - i.1))
        (Fin.append (LinearMap.inl R P Q ∘ p) (LinearMap.inr R P Q ∘ q)) := by
  rw [coe_prodEquivDirectSum_symm_of_tmul]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]
  exact ExteriorAlgebra.ιMulti_mul_ιMulti _ _

universe v' w'

variable {P' : Type v'} {Q' : Type w'}
variable [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q']

/-- The summandwise map on the direct-sum side induced by a pair of linear maps. -/
noncomputable def prodDirectSumMap (k : ℕ) (f : P →ₗ[R] P') (g : Q →ₗ[R] Q') :
    (⨁ i : Fin (k + 1), (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(k - i.1) Q)) →ₗ[R]
      ⨁ i : Fin (k + 1), (⋀[R]^i.1 P') ⊗[R] (⋀[R]^(k - i.1) Q') :=
  DirectSum.lmap fun i ↦
    TensorProduct.map (exteriorPower.map i.1 f) (exteriorPower.map (k - i.1) g)

/-- Naturality of the inverse fixed-degree decomposition for arbitrary module maps over `R`. -/
theorem prodEquivDirectSum_symm_naturality (k : ℕ)
    (f : P →ₗ[R] P') (g : Q →ₗ[R] Q') :
    (exteriorPower.map k (f.prodMap g)).comp
        (prodEquivDirectSum R P Q k).symm.toLinearMap =
      (prodEquivDirectSum R P' Q' k).symm.toLinearMap.comp
        (prodDirectSumMap R P Q k f g) := by
  apply DirectSum.linearMap_ext
  intro i
  apply TensorProduct.ext'
  intro a b
  apply Subtype.ext
  simp only [LinearMap.comp_apply, exteriorPower.coe_map]
  rw [DirectSum.lof_eq_of]
  change ExteriorAlgebra.map (f.prodMap g)
      ((prodEquivDirectSum R P Q k).symm
        (DirectSum.of
          (fun j : Fin (k + 1) ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(k - j.1) Q)) i
          (a ⊗ₜ[R] b))).1 =
    ((prodEquivDirectSum R P' Q' k).symm
      (prodDirectSumMap R P Q k f g
        (DirectSum.of
          (fun j : Fin (k + 1) ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(k - j.1) Q)) i
          (a ⊗ₜ[R] b)))).1
  rw [coe_prodEquivDirectSum_symm_of_tmul]
  simp only [map_mul]
  rw [prodDirectSumMap, DirectSum.lmap_of, TensorProduct.map_tmul]
  rw [coe_prodEquivDirectSum_symm_of_tmul]
  simp only [exteriorPower.coe_map]
  congr 1
  · rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    rw [show (f.prodMap g).comp (LinearMap.inl R P Q) =
        (LinearMap.inl R P' Q').comp f by
          apply LinearMap.ext
          intro x
          simp]
    rw [← ExteriorAlgebra.map_comp_map]
    rfl
  · rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    rw [show (f.prodMap g).comp (LinearMap.inr R P Q) =
        (LinearMap.inr R P' Q').comp g by
          apply LinearMap.ext
          intro x
          simp]
    rw [← ExteriorAlgebra.map_comp_map]
    rfl

/-- Naturality of `prodEquivDirectSum` for arbitrary module maps over the fixed base ring. -/
theorem prodEquivDirectSum_naturality (k : ℕ)
    (f : P →ₗ[R] P') (g : Q →ₗ[R] Q') :
    (prodEquivDirectSum R P' Q' k).toLinearMap.comp
        (exteriorPower.map k (f.prodMap g)) =
      (prodDirectSumMap R P Q k f g).comp
        (prodEquivDirectSum R P Q k).toLinearMap := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (prodEquivDirectSum_symm_naturality R P Q k f g)
    (prodEquivDirectSum R P Q k x)
  have hinv :
      exteriorPower.map k (f.prodMap g) x =
        (prodEquivDirectSum R P' Q' k).symm
          (prodDirectSumMap R P Q k f g (prodEquivDirectSum R P Q k x)) := by
    simp only [LinearMap.comp_apply] at h
    change exteriorPower.map k (f.prodMap g)
        ((prodEquivDirectSum R P Q k).symm (prodEquivDirectSum R P Q k x)) =
      (prodEquivDirectSum R P' Q' k).symm
        (prodDirectSumMap R P Q k f g (prodEquivDirectSum R P Q k x)) at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h
  change prodEquivDirectSum R P' Q' k (exteriorPower.map k (f.prodMap g) x) =
    prodDirectSumMap R P Q k f g (prodEquivDirectSum R P Q k x)
  rw [hinv, LinearEquiv.apply_symm_apply]

end exteriorPower
