/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.RestrictedGeometricInverse
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.KernelFiltration
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Henselian

/-!
# Units of ideal-adically restricted multivariate power series

For an adically complete commutative coefficient ring, a restricted series is a
unit exactly when its first polynomial reduction is a unit. The coefficient
tests below do not require a finite variable type or a finitely generated ideal.
-/

public section

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]

/-- The first polynomial reduction detects units in the existing restricted subring. -/
theorem isUnit_adicallyRestricted_iff_adicReduction_one
    (f : adicallyRestrictedSubring (σ := σ) I) :
    IsUnit f ↔ IsUnit (adicReduction I 1 f) := by
  constructor
  · exact fun hf => hf.map (adicReduction I 1)
  · intro hf
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hf
    obtain ⟨g, hg⟩ := adicReduction_surjective I 1 v
    let h : adicallyRestrictedSubring (σ := σ) I := 1 - f * g
    have hh : adicReduction I 1 h = 0 := by
      simp only [h, map_sub, map_one, map_mul, hg, hv, sub_self]
    let E : Module.End R (adicallyRestrictedSubring (σ := σ) I) :=
      { toFun := fun x => h * x
        map_add' := by intro x y; exact mul_add h x y
        map_smul' := by intro r x; exact mul_smul_comm r h x }
    have hEval (x : adicallyRestrictedSubring (σ := σ) I) : E x = h * x := rfl
    have hE : ∀ n x, adicReduction I n x = 0 →
        adicReduction I (n + 1) (E x) = 0 := by
      intro n x hx
      rw [hEval]
      have step := adicReduction_mul_eq_zero I h x 1 n hh hx
      rw [Nat.add_comm 1 n] at step
      exact step
    let w := restrictedGeometricInverse I E hE 1
    have hw : w - h * w = 1 := by
      have he := congrArg (fun F : Module.End R (adicallyRestrictedSubring (σ := σ) I) => F 1)
        (restrictedGeometricInverse_left_inv I E hE)
      have he' : w - E w = 1 := by
        simpa only [w, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using he
      simpa only [hEval] using he'
    apply isUnit_iff_exists_inv.mpr
    refine ⟨g * w, ?_⟩
    calc
      f * (g * w) = w - h * w := by dsimp [h]; ring
      _ = 1 := hw

/-- Unit detection by coefficients in the quotient by the actual ideal `I`. -/
theorem isUnit_adicallyRestricted_iff_coeff_mod_ideal
    (f : adicallyRestrictedSubring (σ := σ) I) :
    IsUnit f ↔
      IsUnit (Ideal.Quotient.mk I (coeff 0 (f : MvPowerSeries σ R))) ∧
        ∀ α : σ →₀ ℕ, α ≠ 0 →
          IsNilpotent (Ideal.Quotient.mk I (coeff α (f : MvPowerSeries σ R))) := by
  rw [isUnit_adicallyRestricted_iff_adicReduction_one I f, MvPolynomial.isUnit_iff]
  have hpow : I ^ 1 = I := Submodule.pow_one I
  simp only [coeff_adicReduction]
  rw [hpow]

/-- In a complete coefficient ring, reduction modulo `I` reflects scalar units. -/
theorem isUnit_iff_quotient_of_isAdicComplete (r : R) :
    IsUnit r ↔ IsUnit (Ideal.Quotient.mk I r) := by
  haveI : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
  exact ⟨fun hr => hr.map _, fun hr => isUnit_of_map_unit _ r hr⟩

/-- Unit detection by an actual scalar unit and radical containment of all
nonconstant coefficients. -/
theorem isUnit_adicallyRestricted_iff_coeff_radical
    (f : adicallyRestrictedSubring (σ := σ) I) :
    IsUnit f ↔ IsUnit (coeff 0 (f : MvPowerSeries σ R)) ∧
      ∀ α : σ →₀ ℕ, α ≠ 0 → coeff α (f : MvPowerSeries σ R) ∈ I.radical := by
  rw [isUnit_adicallyRestricted_iff_coeff_mod_ideal I f]
  simp only [← isUnit_iff_quotient_of_isAdicComplete I,
    IsNilpotent, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_radical_iff]

end MvPowerSeries
