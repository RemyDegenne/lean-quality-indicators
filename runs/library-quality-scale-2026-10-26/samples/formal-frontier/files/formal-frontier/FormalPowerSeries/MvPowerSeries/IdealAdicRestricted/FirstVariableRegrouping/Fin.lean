/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariableRegrouping
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.Rename

public section

/-!
# First-variable regrouping for `Fin (n + 1)`

Variable renaming transports coefficient extraction, polynomial inclusion,
and bounded-degree support between `Fin (n + 1)` and `Option (Fin n)`.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {R σ υ : Type*} [CommRing R]

variable (I : Ideal R) (n : ℕ)

/-- Reindex restricted `Fin (n+1)` series as restricted `Option (Fin n)` series. -/
noncomputable def restrictedFinSuccEquiv :
    adicallyRestrictedSubring (σ := Fin (n + 1)) I ≃+*
      adicallyRestrictedSubring (σ := Option (Fin n)) I :=
  restrictedRenameEquiv I (_root_.finSuccEquiv n)

@[simp]
theorem restrictedFinSuccEquiv_coe
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) I) :
    (restrictedFinSuccEquiv I n f : MvPowerSeries (Option (Fin n)) R) =
      renameEquiv R (_root_.finSuccEquiv n) (f : MvPowerSeries (Fin (n + 1)) R) :=
  restrictedRenameEquiv_coe I _ f

/-- Extract a restricted coefficient series in the first `Fin (n+1)` variable. -/
noncomputable def restrictedFinFirstCoeff (i : ℕ) :
    adicallyRestrictedSubring (σ := Fin (n + 1)) I →+
      adicallyRestrictedSubring (σ := Fin n) I :=
  (restrictedFirstCoeff I i).comp (restrictedFinSuccEquiv I n).toAddMonoidHom

/-- Regroup restricted `Fin (n+1)` series after explicitly reindexing the variables. -/
noncomputable def restrictedFinFirstRegroup :
    adicallyRestrictedSubring (σ := Fin (n + 1)) I →+*
      PowerSeries (adicallyRestrictedSubring (σ := Fin n) I) :=
  (restrictedFirstRegroup I).comp (restrictedFinSuccEquiv I n).toRingHom

/-- The first-variable coefficients of the Fin regrouping are themselves
restricted series in the remaining variables. -/
@[simp]
theorem coeff_restrictedFinFirstRegroup
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) I) (i : ℕ) :
    PowerSeries.coeff i (restrictedFinFirstRegroup I n f) =
      restrictedFinFirstCoeff I n i f := by
  change PowerSeries.coeff i (restrictedFirstRegroup I (restrictedFinSuccEquiv I n f)) =
    restrictedFirstCoeff I i (restrictedFinSuccEquiv I n f)
  exact coeff_restrictedFirstRegroup I _ i

/-- Regrouping by the first Fin variable retains every coefficient. -/
theorem restrictedFinFirstRegroup_injective :
    Function.Injective (restrictedFinFirstRegroup I n) := by
  intro f g h
  apply (restrictedFinSuccEquiv I n).injective
  apply restrictedFirstRegroup_injective I
  change restrictedFirstRegroup I (restrictedFinSuccEquiv I n f) =
    restrictedFirstRegroup I (restrictedFinSuccEquiv I n g) at h
  exact h

theorem coeff_restrictedFinFirstCoeff (i : ℕ)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) I)
    (β : Fin n →₀ ℕ) :
    coeff β (restrictedFinFirstCoeff I n i f : MvPowerSeries (Fin n) R) =
      coeff (β.cons i) (f : MvPowerSeries (Fin (n + 1)) R) := by
  have h := coeff_coeff_finSuccEquiv (R := R) (n := n)
    (p := (f : MvPowerSeries (Fin (n + 1)) R)) (k := i) (x := β)
  change coeff β (restrictedFirstCoeff I i (restrictedFinSuccEquiv I n f) :
    MvPowerSeries (Fin n) R) = _
  rw [coeff_restrictedFirstCoeff]
  rw [restrictedFinSuccEquiv_coe]
  simpa only [MvPowerSeries.finSuccEquiv, AlgEquiv.trans_apply,
    coeff_coeff_optionEquivLeft] using h

/-- Forgetting the restricted coefficients makes the Fin regrouping commute
with mathlib's raw `finSuccEquiv` after the explicit variable reindexing. -/
theorem map_restrictedFinFirstRegroup_raw
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) I) :
    PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := Fin n) I))
        (restrictedFinFirstRegroup I n f) =
      finSuccEquiv R n (f : MvPowerSeries (Fin (n + 1)) R) := by
  apply PowerSeries.ext
  intro i
  apply MvPowerSeries.ext
  intro β
  rw [PowerSeries.coeff_map]
  change coeff β (↑(PowerSeries.coeff i
    (restrictedFirstRegroup I (restrictedFinSuccEquiv I n f)) :
      adicallyRestrictedSubring (σ := Fin n) I) : MvPowerSeries (Fin n) R) = _
  rw [coeff_restrictedFirstRegroup]
  change coeff β (restrictedFinFirstCoeff I n i f : MvPowerSeries (Fin n) R) =
    coeff β (PowerSeries.coeff i
      (finSuccEquiv R n (f : MvPowerSeries (Fin (n + 1)) R)))
  exact (coeff_restrictedFinFirstCoeff I n i f β).trans
    (coeff_coeff_finSuccEquiv (R := R) (n := n)
      (p := (f : MvPowerSeries (Fin (n + 1)) R)) (k := i) (x := β)).symm

/-- Include finite polynomials over restricted `Fin n` series in restricted
`Fin (n+1)` series without asserting a full iterated restricted equivalence. -/
noncomputable def polynomialRestrictedFinFirst :
    Polynomial (adicallyRestrictedSubring (σ := Fin n) I) →+*
      adicallyRestrictedSubring (σ := Fin (n + 1)) I :=
  (restrictedFinSuccEquiv I n).symm.toRingHom.comp (polynomialRestrictedFirst I)

theorem coeff_polynomialRestrictedFinFirst
    (P : Polynomial (adicallyRestrictedSubring (σ := Fin n) I))
    (i : ℕ) (β : Fin n →₀ ℕ) :
    coeff (β.cons i)
        (polynomialRestrictedFinFirst I n P : MvPowerSeries (Fin (n + 1)) R) =
      coeff β (P.coeff i : MvPowerSeries (Fin n) R) := by
  have h := coeff_restrictedFinFirstCoeff I n i
    (polynomialRestrictedFinFirst I n P) β
  have hEq : restrictedFinFirstCoeff I n i (polynomialRestrictedFinFirst I n P) =
      P.coeff i := by
    change restrictedFirstCoeff I i
      ((restrictedFinSuccEquiv I n)
        ((restrictedFinSuccEquiv I n).symm (polynomialRestrictedFirst I P))) = P.coeff i
    rw [RingEquiv.apply_symm_apply]
    exact restrictedFirstCoeff_polynomialRestrictedFirst I P i
  simpa only [hEq] using h.symm

theorem polynomialRestrictedFinFirst_injective :
    Function.Injective (polynomialRestrictedFinFirst I n) :=
  (restrictedFinSuccEquiv I n).symm.injective.comp (polynomialRestrictedFirst_injective I)

/-- Actual vanishing at all first exponents `≥ d` characterizes the unique
degree-`< d` polynomial, including `d = 0` over the zero ring. -/
theorem restrictedFinFirst_actual_support_iff
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) I) (d : ℕ) :
    (∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
      coeff (β.cons i) (f : MvPowerSeries (Fin (n + 1)) R) = 0) ↔
      ∃! P : Polynomial (adicallyRestrictedSubring (σ := Fin n) I),
        P.degree < (d : WithBot ℕ) ∧ polynomialRestrictedFinFirst I n P = f := by
  constructor
  · intro hv
    have hOption : ∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
        coeff (β.optionElim i)
          (restrictedFinSuccEquiv I n f : MvPowerSeries (Option (Fin n)) R) = 0 := by
      intro i β hi
      rw [← coeff_restrictedFirstCoeff I (restrictedFinSuccEquiv I n f) i β]
      change coeff β (restrictedFinFirstCoeff I n i f : MvPowerSeries (Fin n) R) = 0
      rw [coeff_restrictedFinFirstCoeff]
      exact hv i β hi
    obtain ⟨P, ⟨hdegree, heq⟩, _⟩ :=
      (restrictedFirst_actual_support_iff I (restrictedFinSuccEquiv I n f) d).mp hOption
    have hImage : polynomialRestrictedFinFirst I n P = f := by
      apply (restrictedFinSuccEquiv I n).injective
      change (restrictedFinSuccEquiv I n)
        ((restrictedFinSuccEquiv I n).symm (polynomialRestrictedFirst I P)) =
          (restrictedFinSuccEquiv I n) f
      simpa only [RingEquiv.apply_symm_apply] using heq
    refine ⟨P, ⟨hdegree, hImage⟩, ?_⟩
    intro Q hQ
    exact polynomialRestrictedFinFirst_injective I n (hQ.2.trans hImage.symm)
  · rintro ⟨P, ⟨hdegree, heq⟩, _⟩ i β hi
    rw [← heq, coeff_polynomialRestrictedFinFirst]
    have hz : P.coeff i = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero P d).mp hdegree i hi
    simp only [hz, Subring.coe_zero, coeff_zero]

end MvPowerSeries
