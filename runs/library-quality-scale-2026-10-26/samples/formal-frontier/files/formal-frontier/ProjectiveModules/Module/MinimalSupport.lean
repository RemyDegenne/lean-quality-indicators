/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Bases of minimal support

This file records a small choice principle used in local-projective arguments:
for a fixed vector in a free module, one may choose a basis (with a fixed index
type) in which the vector has support of least finite cardinality.
-/

@[expose] public section

universe uR uM uι

namespace Module.Basis

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {ι : Type uι}

/-- A basis has minimal support for `x` if no basis with the same index type
expresses `x` using fewer nonzero coordinates. -/
def HasMinimalSupport (b : Basis ι R M) (x : M) : Prop :=
  ∀ b' : Basis ι R M, (b.repr x).support.card ≤ (b'.repr x).support.card

/-- Every vector admits a basis of minimal support among bases with a fixed
index type, provided one such basis exists. -/
theorem exists_hasMinimalSupport (b₀ : Basis ι R M) (x : M) :
    ∃ b : Basis ι R M, b.HasMinimalSupport x := by
  classical
  let p : ℕ → Prop := fun n ↦ ∃ b : Basis ι R M, (b.repr x).support.card = n
  have hp : ∃ n, p n := ⟨(b₀.repr x).support.card, b₀, rfl⟩
  obtain ⟨b, hb⟩ := Nat.find_spec hp
  refine ⟨b, fun b' ↦ ?_⟩
  rw [hb]
  exact Nat.find_min' hp ⟨b', rfl⟩

/-- In a minimal-support basis, a nonzero coordinate cannot be recovered by a
linear functional that vanishes on the corresponding basis vector.

The elementary change of basis is the transvection
`z ↦ z + φ z • b j`. If `φ (b j) = 0` and the `j`th coordinate of `x` equals
`φ x`, then the inverse transvection erases exactly that coordinate and leaves
all others unchanged, contradicting minimality. -/
theorem HasMinimalSupport.coord_ne_apply_of_apply_eq_zero
    {b : Basis ι R M} {x : M} (hb : b.HasMinimalSupport x)
    {j : ι} (hj : j ∈ (b.repr x).support)
    (φ : M →ₗ[R] R) (hφj : φ (b j) = 0) :
    b.repr x j ≠ φ x := by
  classical
  intro hcoord
  let e : M ≃ₗ[R] M := LinearEquiv.transvection hφj
  let b' : Basis ι R M := b.map e
  have hrepr : b'.repr x = (b.repr x).erase j := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [b', e, LinearEquiv.transvection.symm_eq,
        LinearMap.transvection.apply, hφj, hcoord]
    · simp [b', e, LinearEquiv.transvection.symm_eq,
        LinearMap.transvection.apply, hφj, hkj]
  have hle := hb b'
  rw [hrepr, Finsupp.support_erase] at hle
  exact (Nat.not_lt_of_ge hle) (Finset.card_erase_lt_of_mem hj)

/-- A nonzero coordinate in a minimal-support basis is not a right-linear
combination of the remaining coordinates. For a module over `Rᵐᵒᵖ`, this is
exactly the left-ideal coefficient orientation for a right `R`-module. -/
theorem HasMinimalSupport.coord_ne_sum_mul
    [DecidableEq ι]
    {b : Basis ι R M} {x : M} (hb : b.HasMinimalSupport x)
    {j : ι} (hj : j ∈ (b.repr x).support) (c : ι → R) :
    b.repr x j ≠
      ∑ i ∈ (b.repr x).support.erase j, b.repr x i * c i := by
  classical
  let φ : M →ₗ[R] R := b.constr ℕ fun i ↦
    if i ∈ (b.repr x).support.erase j then c i else 0
  have hφj : φ (b j) = 0 := by
    simp [φ]
  have hne := hb.coord_ne_apply_of_apply_eq_zero hj φ hφj
  have hφx : φ x =
      ∑ i ∈ (b.repr x).support.erase j, b.repr x i * c i := by
    simp only [φ, Basis.constr_apply, Finsupp.sum, smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext i
      simp
    · intro i hi
      rfl
  intro h
  exact hne (h.trans hφx.symm)

/-- An off-diagonal coefficient of a projection fixing `x`, measured in a
minimal-support basis and between two coordinates in the support of `x`, cannot
be a unit. -/
theorem HasMinimalSupport.not_isUnit_coord_comp_apply_of_ne
    {b : Basis ι R M} {x : M} (hb : b.HasMinimalSupport x)
    (e : M →ₗ[R] M) (hex : e x = x)
    {i j : ι} (hi : i ∈ (b.repr x).support) (hij : i ≠ j) :
    ¬ IsUnit (b.coord j (e (b i))) := by
  classical
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  let L : M →ₗ[R] R := (b.coord j).comp e
  let φ : M →ₗ[R] R :=
    b.coord i + (LinearMap.mulRight R (↑u⁻¹ : R)).comp (b.coord j - L)
  have hφi : φ (b i) = 0 := by
    simp only [φ, L, LinearMap.add_apply, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_eq_same, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.mulRight_apply, LinearMap.sub_apply]
    rw [Finsupp.single_eq_of_ne hij.symm, zero_sub]
    change (↑u : R) = (b.repr (e (b i))) j at hu
    rw [← hu]
    simp
  have hφx : φ x = b.repr x i := by
    simp [φ, L, hex]
  exact hb.coord_ne_apply_of_apply_eq_zero hi φ hφi hφx.symm

/-- The complement of a diagonal coefficient of a projection fixing `x`, in a
minimal-support coordinate of `x`, cannot be a unit. -/
theorem HasMinimalSupport.not_isUnit_one_sub_coord_comp_apply
    {b : Basis ι R M} {x : M} (hb : b.HasMinimalSupport x)
    (e : M →ₗ[R] M) (hex : e x = x)
    {j : ι} (hj : j ∈ (b.repr x).support) :
    ¬ IsUnit (1 - b.coord j (e (b j))) := by
  classical
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  let L : M →ₗ[R] R := (b.coord j).comp e
  let φ : M →ₗ[R] R :=
    b.coord j - (LinearMap.mulRight R (↑u⁻¹ : R)).comp (b.coord j - L)
  have hφj : φ (b j) = 0 := by
    simp only [φ, L, LinearMap.sub_apply, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_eq_same, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.mulRight_apply]
    change (↑u : R) = 1 - (b.repr (e (b j))) j at hu
    rw [← hu]
    simp
  have hφx : φ x = b.repr x j := by
    simp [φ, L, hex]
  exact hb.coord_ne_apply_of_apply_eq_zero hj φ hφj hφx.symm

end Module.Basis
