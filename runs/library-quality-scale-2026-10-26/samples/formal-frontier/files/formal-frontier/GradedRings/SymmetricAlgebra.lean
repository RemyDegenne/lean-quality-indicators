/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The natural grading on a symmetric algebra

This file equips `SymmetricAlgebra R M` with its basis-free grading by total degree.  The
degree-`n` component is the `n`-th power of the range of the canonical linear map
`SymmetricAlgebra.ι R M`.
-/

public section

open scoped DirectSum

namespace SymmetricAlgebra

universe u v

variable {R : Type u} {M : Type v}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The degree-`n` part of a symmetric algebra: the `n`-th power of the submodule spanned by
its canonical generators. -/
abbrev homogeneousSubmodule (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ n

variable (R M)

/-- A version of `SymmetricAlgebra.ι` with codomain the direct sum of the natural degree
components. -/
@[expose]
nonrec def GradedAlgebra.ι :
    M →ₗ[R] ⨁ n : ℕ, ↥(homogeneousSubmodule (R := R) (M := M) n) :=
  DirectSum.lof R ℕ
      (fun n ↦ ↥(homogeneousSubmodule (R := R) (M := M) n)) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ fun m ↦ by
      simpa only [homogeneousSubmodule, pow_one] using
        LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of
        (fun n ↦ ↥(homogeneousSubmodule (R := R) (M := M) n)) 1
        ⟨SymmetricAlgebra.ι R M m, by
          simpa only [homogeneousSubmodule, pow_one] using
            LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m⟩ :=
  rfl

variable {R M}

/-- The symmetric algebra is naturally graded by powers of the range of its canonical
degree-one generators. -/
instance gradedAlgebra :
    GradedAlgebra (homogeneousSubmodule (R := R) (M := M)) :=
  fast_instance% GradedAlgebra.ofAlgHom _ (lift <| GradedAlgebra.ι R M)
    (by
      ext m
      change DirectSum.coeAlgHom _
          (lift (GradedAlgebra.ι R M) (SymmetricAlgebra.ι R M m)) =
        SymmetricAlgebra.ι R M m
      rw [lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.coeAlgHom_of,
        Subtype.coe_mk])
    fun n x ↦ by
      obtain ⟨x, hx⟩ := x
      dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
      induction hx using Submodule.pow_induction_on_left' with
      | algebraMap r =>
          rw [AlgHom.commutes, DirectSum.algebraMap_apply]
          rfl
      | add x y n hx hy ihx ihy =>
          rw [map_add, ihx, ihy, ← map_add]
          rfl
      | mem_mul m hm n x hx ih =>
          obtain ⟨_, rfl⟩ := hm
          rw [map_mul, ih, lift_ι_apply, GradedAlgebra.ι_apply R M,
            DirectSum.of_mul_of]
          exact DirectSum.of_eq_of_gradedMonoid_eq
            (Sigma.subtype_ext (add_comm _ _) rfl)

section Map

universe w

variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- The algebra map on symmetric algebras induced by a linear map. -/
@[expose]
def map (f : M →ₗ[R] N) : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N :=
  lift (SymmetricAlgebra.ι R N ∘ₗ f)

@[simp]
theorem map_ι_apply (f : M →ₗ[R] N) (m : M) :
    map f (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (f m) := by
  simp [map]

@[simp]
theorem map_id : map (LinearMap.id (R := R) (M := M)) = AlgHom.id R (SymmetricAlgebra R M) := by
  apply algHom_ext
  ext m
  simp

@[simp]
theorem map_comp {P : Type*} [AddCommMonoid P] [Module R P]
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    map (g.comp f) = (map g).comp (map f) := by
  apply algHom_ext
  ext m
  simp

/-- A linear map sends every homogeneous component of the source symmetric algebra into the
component of the same degree in the target. -/
theorem map_mem_homogeneousSubmodule (f : M →ₗ[R] N) {n : ℕ}
    {x : SymmetricAlgebra R M} (hx : x ∈ homogeneousSubmodule (R := R) (M := M) n) :
    map f x ∈ homogeneousSubmodule (R := R) (M := N) n := by
  have h₁ : Submodule.map (map f).toLinearMap
      (LinearMap.range (SymmetricAlgebra.ι R M)) ≤
      LinearMap.range (SymmetricAlgebra.ι R N) := by
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨f m, (map_ι_apply f m).symm⟩
  have hpow := pow_le_pow_left' h₁ n
  rw [← Submodule.map_pow] at hpow
  exact hpow ⟨x, hx, rfl⟩

/-- The functorial map on symmetric algebras, bundled as a degree-preserving algebra map. -/
@[expose]
def gradedMap (f : M →ₗ[R] N) :
    homogeneousSubmodule (R := R) (M := M) →ₐᵍ[R]
      homogeneousSubmodule (R := R) (M := N) where
  toAlgHom := map f
  map_mem := map_mem_homogeneousSubmodule f

@[simp]
theorem gradedMap_apply (f : M →ₗ[R] N) (x : SymmetricAlgebra R M) :
    gradedMap f x = map f x :=
  rfl

/-- A linear equivalence induces an algebra equivalence of symmetric algebras. -/
@[expose]
def congr (e : M ≃ₗ[R] N) : SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N :=
  AlgEquiv.ofAlgHom (map e) (map e.symm)
    (by
      rw [← map_comp]
      simp)
    (by
      rw [← map_comp]
      simp)

@[simp]
theorem congr_apply (e : M ≃ₗ[R] N) (x : SymmetricAlgebra R M) :
    congr e x = map e x :=
  rfl

@[simp]
theorem congr_symm_apply (e : M ≃ₗ[R] N) (x : SymmetricAlgebra R N) :
    (congr e).symm x = map e.symm x :=
  rfl

end Map

section Basis

universe w

variable {I : Type w}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A basis presentation of a symmetric algebra preserves total degree. -/
theorem equivMvPolynomial_mem_homogeneousSubmodule (b : Module.Basis I R M) {n : ℕ}
    {x : SymmetricAlgebra R M} (hx : x ∈ homogeneousSubmodule (R := R) (M := M) n) :
    equivMvPolynomial b x ∈ MvPolynomial.homogeneousSubmodule I R n := by
  have h₁ : Submodule.map (equivMvPolynomial b).toLinearMap
      (LinearMap.range (SymmetricAlgebra.ι R M)) ≤
      MvPolynomial.homogeneousSubmodule I R 1 := by
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    have hm : m ∈ Submodule.span R (Set.range b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm =>
        rcases hm with ⟨i, rfl⟩
        change equivMvPolynomial b (SymmetricAlgebra.ι R M (b i)) ∈
          Submodule.span R (Set.range MvPolynomial.X)
        rw [equivMvPolynomial_ι_apply]
        exact Submodule.subset_span (Set.mem_range_self i)
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul r x _ hx => simpa using Submodule.smul_mem _ r hx
  have hpow := pow_le_pow_left' h₁ n
  rw [← MvPolynomial.homogeneousSubmodule_one_pow]
  apply hpow
  have hx' : equivMvPolynomial b x ∈
      Submodule.map (equivMvPolynomial b).toAlgHom.toLinearMap
        (LinearMap.range (SymmetricAlgebra.ι R M) ^ n) :=
    ⟨x, hx, rfl⟩
  rw [Submodule.map_pow] at hx'
  exact hx'

/-- The inverse of a basis presentation of a symmetric algebra also preserves total degree. -/
theorem equivMvPolynomial_symm_mem_homogeneousSubmodule (b : Module.Basis I R M) {n : ℕ}
    {p : MvPolynomial I R} (hp : p ∈ MvPolynomial.homogeneousSubmodule I R n) :
    (equivMvPolynomial b).symm p ∈ homogeneousSubmodule (R := R) (M := M) n := by
  have h₁ : Submodule.map (equivMvPolynomial b).symm.toLinearMap
      (MvPolynomial.homogeneousSubmodule I R 1) ≤
      LinearMap.range (SymmetricAlgebra.ι R M) := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, LinearMap.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    change (equivMvPolynomial b).symm (MvPolynomial.X i) ∈
      LinearMap.range (SymmetricAlgebra.ι R M)
    rw [equivMvPolynomial_symm_X]
    exact LinearMap.mem_range_self (SymmetricAlgebra.ι R M) (b i)
  have hpow := pow_le_pow_left' h₁ n
  apply hpow
  have hp' : (equivMvPolynomial b).symm p ∈
      Submodule.map (equivMvPolynomial b).symm.toAlgHom.toLinearMap
        ((MvPolynomial.homogeneousSubmodule I R 1) ^ n) := by
    rw [MvPolynomial.homogeneousSubmodule_one_pow]
    exact ⟨p, hp, rfl⟩
  rw [Submodule.map_pow] at hp'
  exact hp'

/-- A basis presentation of a symmetric algebra, bundled as a degree-preserving algebra map. -/
@[expose]
noncomputable def equivMvPolynomialGradedHom (b : Module.Basis I R M) :
    homogeneousSubmodule (R := R) (M := M) →ₐᵍ[R]
      MvPolynomial.homogeneousSubmodule I R where
  toAlgHom := equivMvPolynomial b
  map_mem := equivMvPolynomial_mem_homogeneousSubmodule b

@[simp]
theorem equivMvPolynomialGradedHom_apply (b : Module.Basis I R M)
    (x : SymmetricAlgebra R M) :
    equivMvPolynomialGradedHom b x = equivMvPolynomial b x :=
  rfl

/-- The inverse basis presentation, bundled as a degree-preserving algebra map. -/
@[expose]
noncomputable def equivMvPolynomialSymmGradedHom (b : Module.Basis I R M) :
    MvPolynomial.homogeneousSubmodule I R →ₐᵍ[R]
      homogeneousSubmodule (R := R) (M := M) where
  toAlgHom := (equivMvPolynomial b).symm
  map_mem := equivMvPolynomial_symm_mem_homogeneousSubmodule b

@[simp]
theorem equivMvPolynomialSymmGradedHom_apply (b : Module.Basis I R M)
    (p : MvPolynomial I R) :
    equivMvPolynomialSymmGradedHom b p = (equivMvPolynomial b).symm p :=
  rfl

end Basis

end SymmetricAlgebra
