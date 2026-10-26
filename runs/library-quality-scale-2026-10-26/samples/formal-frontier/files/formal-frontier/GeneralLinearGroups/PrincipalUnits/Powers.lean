/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.PrincipalUnits
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import AdicModules.RingTheory.Ideal.IsPrincipalPowQuotient

/-!
# Coefficients of principal-unit power layers

Let `I` be a nonzero principal ideal in a commutative domain, contained in the
Jacobson radical, and let `π` be a supplied generator of `I`. At a positive
exponent `n`, the quotient of the original-ring principal units at `I ^ n` by
those at `I ^ (n + 1)` has additive coefficient ring `R ⧸ I`, written
multiplicatively. The coefficient of `1 + a * π ^ n` is the class of `a`.
The quotient uses the stabilizers and coordinate kernel from
`Ideal.principalUnitsQuotientEquiv`. By `Ideal.principalUnitsToQuotient_ker`,
its denominator is the relative deeper stabilizer subgroup; its normality is
`Ideal.principalUnits_subgroupOf_normal`, not an extra hypothesis.

Changing the generator to `u * π` multiplies the forward coordinate of a fixed
unit class by the inverse `n`th power of the residue unit. In contrast, the
inverse parameterization at a fixed coefficient changes by its `n`th power.
Both coordinates have the same quotient domain because the ideal is fixed.

## Implementation notes

The coefficient construction combines `Ideal.principalUnitsQuotientEquiv`
with the inverse of Mathlib's `Ideal.quotEquivPowQuotPowSucc`, transporting
its denominator and rescaling from its chosen generator to the supplied `π`.
A proof of principality obtained from `I = Ideal.span {π}` does not make
Mathlib's chosen generator equal to `π`. The coefficient ring need not be a
field. No local-ring, valuation, completeness or finiteness assumption is used.
The nonzero ideal and domain hypotheses support cancellation in the coefficient
identification. Positivity gives `n + 1 ≤ 2 * n`, which kills the quadratic term.
At exponent zero the quotient of units by principal units is multiplicative
reduction, not this additive layer.

## References

* Fesenko and Vostokov, *Local Fields and Their Extensions*, second edition,
  Chapter I, (5.4)(3), for the positive successive-layer coefficient formula.
* The ideal-layer equivalence in `GeneralLinearGroups.PrincipalUnits`.
* Yakov Pechersky's principal-power quotient equivalences in
  `Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient`.
* The [Adic Modules library](https://github.com/FormalFrontier/adic-modules),
  [`AdicModules.RingTheory.Ideal.IsPrincipalPowQuotient`](https://github.com/FormalFrontier/adic-modules/blob/d0ce9c7ea73e0f995d7318e448af3e14f2e473bd/AdicModules/RingTheory/Ideal/IsPrincipalPowQuotient.lean),
  for the chosen-generator forward and inverse representative formulas for
  that Mathlib equivalence, including
  `Ideal.quotEquivPowQuotPowSucc_symm_apply_mk`.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Coefficients in `R ⧸ I` of the positive successive principal-unit layer,
relative to the supplied generator `π` of a nonzero ideal in the Jacobson
radical. On the original-ring unit `1 + a * π ^ n` the coordinate is `[a]`.
This is the principal-ideal coefficient form of Fesenko–Vostokov, I.(5.4)(3). -/
noncomputable def principalUnitsPowQuotientEquiv [IsDomain R] (I : Ideal R)
    (hI : I ≠ ⊥)
    (hJ : I ≤ Ideal.jacobson ⊥) (π : R) (hgen : I = Ideal.span {π})
    (n : ℕ) (hpos : 1 ≤ n) :
    MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ (I ^ n : Ideal R)) ⧸
        ((I ^ n).principalUnitsToQuotient (I ^ (n + 1)) (by
          rw [← pow_mul]
          exact Ideal.pow_le_pow_right (by
            simpa only [Nat.mul_two] using Nat.add_le_add_left hpos n))).ker ≃*
      Multiplicative (R ⧸ I) := by
  classical
  let h : I.IsPrincipal := ⟨π, hgen⟩
  let g : R := h.principal.choose
  have hg : I = Ideal.span {g} := h.principal.choose_spec
  have hw : ∃ w : Rˣ, π = (w : R) * g := by
    obtain ⟨w, hw⟩ :=
      Ideal.span_singleton_eq_span_singleton.mp (hg.symm.trans hgen)
    exact ⟨w, hw.symm.trans (mul_comm g (w : R))⟩
  let w : Rˣ := hw.choose
  have hden :
      Submodule.comap (I ^ n : Ideal R).subtype (I ^ (n + 1)) =
        (I • ⊤ : Submodule R (I ^ n : Ideal R)) := by
    ext x
    change (x : R) ∈ I ^ (n + 1) ↔
      x ∈ (I • ⊤ : Submodule R (I ^ n : Ideal R))
    rw [Submodule.mem_smul_top_iff, Ideal.smul_eq_mul, ← pow_succ']
  let transport := Submodule.quotEquivOfEq _ _ hden
  let e := Ideal.quotEquivPowQuotPowSucc h hI n
  let wbar : (R ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom w
  -- Since π = (w : R) * g, the g-coordinate is the π-coordinate times wbar ^ n.
  -- Rescaling uses a residue unit, not an inverse of an arbitrary coefficient.
  let rescale : (R ⧸ I) ≃ₗ[R ⧸ I] (R ⧸ I) :=
    LinearEquiv.smulOfUnit (wbar⁻¹ ^ n)
  have hsq : (I ^ n) ^ 2 ≤ I ^ (n + 1) := by
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by
      simpa only [Nat.mul_two] using Nat.add_le_add_left hpos n)
  have hJac : I ^ n ≤ Ring.jacobson R := by
    rw [← Ideal.jacobson_bot]
    exact (Ideal.pow_le_self
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hpos))).trans hJ
  exact ((I ^ n).principalUnitsQuotientEquiv (I ^ (n + 1)) hsq hJac).trans
    (AddEquiv.toMultiplicative
      ((transport.trans e.symm).toAddEquiv.trans rescale.toAddEquiv))

variable [IsDomain R]

/-- The forward coefficient of the Jacobson lift with value `1 + a * π ^ n`
is the class of `a` modulo `I`. -/
@[simp]
theorem principalUnitsPowQuotientEquiv_mk (I : Ideal R) (hI : I ≠ ⊥)
    (hJ : I ≤ Ideal.jacobson ⊥) (π : R) (hgen : I = Ideal.span {π})
    (n : ℕ) (hpos : 1 ≤ n) (a : R) :
    I.principalUnitsPowQuotientEquiv hI hJ π hgen n hpos
        (QuotientGroup.mk ((I ^ n).principalUnitsMk
          (by
            rw [← Ideal.jacobson_bot]
            exact (Ideal.pow_le_self
              (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hpos))).trans hJ)
          (⟨a * π ^ n, Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
            (hgen.ge (Ideal.mem_span_singleton_self π)) n)⟩ : (I ^ n : Ideal R)))) =
      Multiplicative.ofAdd (Ideal.Quotient.mk I a) := by
  classical
  let h : I.IsPrincipal := ⟨π, hgen⟩
  let g : R := h.principal.choose
  have hg : I = Ideal.span {g} := h.principal.choose_spec
  have hw : ∃ w : Rˣ, π = (w : R) * g := by
    obtain ⟨w, hw⟩ :=
      Ideal.span_singleton_eq_span_singleton.mp (hg.symm.trans hgen)
    exact ⟨w, hw.symm.trans (mul_comm g (w : R))⟩
  let w : Rˣ := hw.choose
  have hπ : π = (w : R) * g := hw.choose_spec
  have hden :
      Submodule.comap (I ^ n : Ideal R).subtype (I ^ (n + 1)) =
        (I • ⊤ : Submodule R (I ^ n : Ideal R)) := by
    ext x
    change (x : R) ∈ I ^ (n + 1) ↔
      x ∈ (I • ⊤ : Submodule R (I ^ n : Ideal R))
    rw [Submodule.mem_smul_top_iff, Ideal.smul_eq_mul, ← pow_succ']
  let transport := Submodule.quotEquivOfEq _ _ hden
  let e := Ideal.quotEquivPowQuotPowSucc h hI n
  let wbar : (R ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom w
  have hsq : (I ^ n) ^ 2 ≤ I ^ (n + 1) := by
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by
      simpa only [Nat.mul_two] using Nat.add_le_add_left hpos n)
  have hJac : I ^ n ≤ Ring.jacobson R := by
    rw [← Ideal.jacobson_bot]
    exact (Ideal.pow_le_self
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hpos))).trans hJ
  let x : (I ^ n : Ideal R) :=
    ⟨a * π ^ n, Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
      (hgen.ge (Ideal.mem_span_singleton_self π)) n)⟩
  let y : (I ^ n : Ideal R) :=
    ⟨(a * (w : R) ^ n) * g ^ n, Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
      (hg.ge (Ideal.mem_span_singleton_self g)) n)⟩
  have hxy : x = y := by
    apply Subtype.ext
    change a * π ^ n = (a * (w : R) ^ n) * g ^ n
    rw [hπ, mul_pow, mul_assoc]
  have htransport : transport (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
    Submodule.quotEquivOfEq_mk _ _ hden x
  -- The released representative formula uses g, not the supplied generator π.
  have he : e.symm (Submodule.Quotient.mk y) =
      Ideal.Quotient.mk I (a * (w : R) ^ n) :=
    Ideal.quotEquivPowQuotPowSucc_symm_apply_mk h hI n (a * (w : R) ^ n)
  have hcoeff : Ideal.Quotient.mk I (a * (w : R) ^ n) =
      (↑(wbar ^ n) : R ⧸ I) * Ideal.Quotient.mk I a := by
    change Ideal.Quotient.mk I (a * (w : R) ^ n) =
      Ideal.Quotient.mk I (w : R) ^ n * Ideal.Quotient.mk I a
    rw [map_mul, map_pow, mul_comm]
  apply Multiplicative.toAdd.injective
  change (↑(wbar⁻¹ ^ n) : R ⧸ I) *
      e.symm (transport (Multiplicative.toAdd
        ((I ^ n).principalUnitsQuotientEquiv (I ^ (n + 1)) hsq hJac
          (QuotientGroup.mk ((I ^ n).principalUnitsMk hJac x))))) =
    Ideal.Quotient.mk I a
  rw [principalUnitsQuotientEquiv_mk, principalUnitsToQuotient_mk, toAdd_ofAdd,
    htransport, hxy, he, hcoeff]
  simpa only [inv_pow] using
    (Units.inv_mul_cancel_left (wbar ^ n) (Ideal.Quotient.mk I a))

/-- The inverse coefficient map sends `[a]` to the class of the original-ring
unit with value `1 + a * π ^ n`. -/
@[simp]
theorem principalUnitsPowQuotientEquiv_symm_mk (I : Ideal R) (hI : I ≠ ⊥)
    (hJ : I ≤ Ideal.jacobson ⊥) (π : R) (hgen : I = Ideal.span {π})
    (n : ℕ) (hpos : 1 ≤ n) (a : R) :
    (I.principalUnitsPowQuotientEquiv hI hJ π hgen n hpos).symm
        (Multiplicative.ofAdd (Ideal.Quotient.mk I a)) =
      QuotientGroup.mk ((I ^ n).principalUnitsMk
        (by
          rw [← Ideal.jacobson_bot]
          exact (Ideal.pow_le_self
            (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hpos))).trans hJ)
        (⟨a * π ^ n, Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
          (hgen.ge (Ideal.mem_span_singleton_self π)) n)⟩ : (I ^ n : Ideal R))) := by
  apply (I.principalUnitsPowQuotientEquiv hI hJ π hgen n hpos).injective
  exact ((I.principalUnitsPowQuotientEquiv hI hJ π hgen n hpos).apply_symm_apply _).trans
    (I.principalUnitsPowQuotientEquiv_mk hI hJ π hgen n hpos a).symm

/-- For a fixed unit-layer class, replacing `π` by `u * π` multiplies its
forward coefficient by the inverse `n`th power of the residue unit. -/
theorem principalUnitsPowQuotientEquiv_unit_mul (I : Ideal R) (hI : I ≠ ⊥)
    (hJ : I ≤ Ideal.jacobson ⊥) (π : R) (hgen : I = Ideal.span {π})
    (n : ℕ) (hpos : 1 ≤ n) (u : Rˣ)
    (q : MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ (I ^ n : Ideal R)) ⧸
      ((I ^ n).principalUnitsToQuotient (I ^ (n + 1)) (by
        rw [← pow_mul]
        exact Ideal.pow_le_pow_right (by
          simpa only [Nat.mul_two] using Nat.add_le_add_left hpos n))).ker) :
    Multiplicative.toAdd
        (I.principalUnitsPowQuotientEquiv hI hJ ((u : R) * π)
          (by
            rw [Ideal.span_singleton_mul_left_unit u.isUnit]
            exact hgen) n hpos q) =
      (↑((Units.map (Ideal.Quotient.mk I).toMonoidHom u)⁻¹ ^ n) : R ⧸ I) *
        Multiplicative.toAdd (I.principalUnitsPowQuotientEquiv hI hJ π hgen n hpos q) := by
  have hgen' : I = Ideal.span {(u : R) * π} := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit]
    exact hgen
  have hJac : I ^ n ≤ Ring.jacobson R := by
    rw [← Ideal.jacobson_bot]
    exact (Ideal.pow_le_self
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hpos))).trans hJ
  let e := I.principalUnitsPowQuotientEquiv hI hJ π hgen n hpos
  let e' := I.principalUnitsPowQuotientEquiv hI hJ ((u : R) * π) hgen' n hpos
  let wbar : (R ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom u
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := I)
    (Multiplicative.toAdd (e' q))
  let x : (I ^ n : Ideal R) :=
    ⟨a * ((u : R) * π) ^ n, Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
      (hgen'.ge (Ideal.mem_span_singleton_self ((u : R) * π))) n)⟩
  let y : (I ^ n : Ideal R) :=
    ⟨(a * (u : R) ^ n) * π ^ n, Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
      (hgen.ge (Ideal.mem_span_singleton_self π)) n)⟩
  have hlift : (I ^ n).principalUnitsMk hJac x =
      (I ^ n).principalUnitsMk hJac y := by
    apply Subtype.ext
    apply Units.ext
    simp only [principalUnitsMk_coe]
    change 1 + a * ((u : R) * π) ^ n = 1 + (a * (u : R) ^ n) * π ^ n
    rw [mul_pow, mul_assoc]
  have hq : QuotientGroup.mk ((I ^ n).principalUnitsMk hJac x) = q := by
    apply e'.injective
    exact (I.principalUnitsPowQuotientEquiv_mk hI hJ ((u : R) * π)
      hgen' n hpos a).trans
      ((congrArg Multiplicative.ofAdd ha).trans (ofAdd_toAdd _))
  have hold : Multiplicative.toAdd (e q) =
      Ideal.Quotient.mk I (a * (u : R) ^ n) := by
    rw [← hq, hlift]
    simpa only [toAdd_ofAdd] using congrArg Multiplicative.toAdd
      (I.principalUnitsPowQuotientEquiv_mk hI hJ π hgen n hpos (a * (u : R) ^ n))
  have hcoeff : Ideal.Quotient.mk I (a * (u : R) ^ n) =
      (↑(wbar ^ n) : R ⧸ I) * Ideal.Quotient.mk I a := by
    change Ideal.Quotient.mk I (a * (u : R) ^ n) =
      Ideal.Quotient.mk I (u : R) ^ n * Ideal.Quotient.mk I a
    rw [map_mul, map_pow, mul_comm]
  change Multiplicative.toAdd (e' q) =
    (↑(wbar⁻¹ ^ n) : R ⧸ I) * Multiplicative.toAdd (e q)
  rw [← ha, hold, hcoeff]
  simpa only [inv_pow] using
    (Units.inv_mul_cancel_left (wbar ^ n) (Ideal.Quotient.mk I a)).symm

/-- For a fixed coefficient parameter, the inverse coordinate for `u * π`
is the inverse coordinate for `π` at the parameter multiplied by the `n`th
power of the residue unit. This differs from the forward change-of-generator law. -/
theorem principalUnitsPowQuotientEquiv_symm_unit_mul (I : Ideal R) (hI : I ≠ ⊥)
    (hJ : I ≤ Ideal.jacobson ⊥) (π : R) (hgen : I = Ideal.span {π})
    (n : ℕ) (hpos : 1 ≤ n) (u : Rˣ) (b : R ⧸ I) :
    (I.principalUnitsPowQuotientEquiv hI hJ ((u : R) * π)
        (by
          rw [Ideal.span_singleton_mul_left_unit u.isUnit]
          exact hgen) n hpos).symm
        (Multiplicative.ofAdd b) =
      (I.principalUnitsPowQuotientEquiv hI hJ π hgen n hpos).symm
        (Multiplicative.ofAdd
          ((↑((Units.map (Ideal.Quotient.mk I).toMonoidHom u) ^ n) : R ⧸ I) * b)) := by
  have hgen' : I = Ideal.span {(u : R) * π} := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit]
    exact hgen
  let e := I.principalUnitsPowQuotientEquiv hI hJ π hgen n hpos
  let e' := I.principalUnitsPowQuotientEquiv hI hJ ((u : R) * π) hgen' n hpos
  let wbar : (R ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom u
  have h := I.principalUnitsPowQuotientEquiv_unit_mul hI hJ π hgen n hpos u
    (e'.symm (Multiplicative.ofAdd b))
  change Multiplicative.toAdd (e' (e'.symm (Multiplicative.ofAdd b))) =
    (↑(wbar⁻¹ ^ n) : R ⧸ I) *
      Multiplicative.toAdd (e (e'.symm (Multiplicative.ofAdd b))) at h
  rw [e'.apply_symm_apply, toAdd_ofAdd] at h
  change e'.symm (Multiplicative.ofAdd b) =
    e.symm (Multiplicative.ofAdd ((↑(wbar ^ n) : R ⧸ I) * b))
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [e.apply_symm_apply, toAdd_ofAdd]
  calc
    Multiplicative.toAdd (e (e'.symm (Multiplicative.ofAdd b))) =
        (↑(wbar ^ n) : R ⧸ I) * ((↑(wbar⁻¹ ^ n) : R ⧸ I) *
          Multiplicative.toAdd (e (e'.symm (Multiplicative.ofAdd b)))) := by
      simpa only [inv_pow] using
        (Units.mul_inv_cancel_left (wbar ^ n)
          (Multiplicative.toAdd (e (e'.symm (Multiplicative.ofAdd b))))).symm
    _ = (↑(wbar ^ n) : R ⧸ I) * b := by rw [← h]

end Ideal
