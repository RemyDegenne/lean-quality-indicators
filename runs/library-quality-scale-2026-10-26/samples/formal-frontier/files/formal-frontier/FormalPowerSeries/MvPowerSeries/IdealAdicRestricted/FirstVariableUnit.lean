/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariableRegrouping.Fin
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.UnitDetection.Residue
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

public section

/-!
# Units of conditional first-variable restricted quotients

A supplied division of the distinguished first-variable monomial `X₀^d` by a
divisor whose regrouped residue has degree `d` and nonzero scalar top `C c`,
with remainder coefficients vanishing at first exponents at least `d`, gives
quotient residue `C (c⁻¹)` over a commutative local ring with `a` in its
maximal ideal. Radical equality and adic completeness additionally reflect
this to a restricted-subring unit.
This does not construct a division or a preparation, including at degree zero.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {R σ : Type*} [CommRing R]

section FirstVariable

variable [IsLocalRing R] (a : R) (ham : a ∈ IsLocalRing.maximalIdeal R) (n : ℕ)

/-- Reduction and the first-variable finite-polynomial embedding commute
coefficientwise. This does not assert an iterated restricted-ring equivalence. -/
theorem finSuccEquiv_restrictedResidueHom_polynomialRestrictedFinFirst
    (P : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))) :
    MvPolynomial.finSuccEquiv (R ⧸ IsLocalRing.maximalIdeal R) n
        (restrictedResidueHom (σ := Fin (n + 1)) a ham
          (polynomialRestrictedFinFirst (Ideal.span {a}) n P)) =
      P.map (restrictedResidueHom (σ := Fin n) a ham) := by
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro β
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, Polynomial.coeff_map,
    coeff_restrictedResidueHom, coeff_polynomialRestrictedFinFirst,
    coeff_restrictedResidueHom]

end FirstVariable

section PolynomialQuotient

variable {k : Type*} [CommRing k] [IsDomain k] (n d : ℕ)

private theorem quotient_eq_constant_of_scalar_top
    (F Q B : Polynomial (MvPolynomial (Fin n) k)) (c cInv : k)
    (hc : c ≠ 0) (hcInv : c * cInv = 1)
    (hdegree : F.natDegree = d) (htop : F.coeff d = MvPolynomial.C c)
    (hB : B.degree < (d : WithBot ℕ))
    (heq : Polynomial.X ^ d = Q * F + B) :
    Q = Polynomial.C (MvPolynomial.C cInv) := by
  have htopNonzero : (MvPolynomial.C c : MvPolynomial (Fin n) k) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr hc
  have hF : F ≠ 0 := by
    intro hz
    apply htopNonzero
    simpa only [htop, Polynomial.coeff_zero] using congrArg (fun p => p.coeff d) hz
  have hQ : Q ≠ 0 := by
    intro hz
    have hB_eq : B = Polynomial.X ^ d := by simpa only [hz, zero_mul, zero_add] using heq.symm
    rw [hB_eq, Polynomial.degree_X_pow] at hB
    exact (lt_irrefl _) hB
  have hprod : (Q * F).degree ≤ (d : WithBot ℕ) := by
    have hmul : Q * F = Polynomial.X ^ d - B := by
      calc
        Q * F = (Q * F + B) - B := (add_sub_cancel_right _ _).symm
        _ = Polynomial.X ^ d - B := by rw [← heq]
    rw [hmul]
    exact (Polynomial.degree_sub_le _ _).trans
      (max_le (by simp only [Polynomial.degree_X_pow, le_refl]) hB.le)
  have hQzero : Q.natDegree = 0 := by
    have hnat := Polynomial.natDegree_le_of_degree_le hprod
    rw [Polynomial.natDegree_mul hQ hF, hdegree] at hnat
    omega
  have hQconst : Q = Polynomial.C (Q.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hQzero
  have hBcoeff : B.coeff d = 0 :=
    (Polynomial.degree_lt_iff_coeff_zero B d).mp hB d le_rfl
  have hprodTop : Q.coeff 0 * MvPolynomial.C c = 1 := by
    have hx := congrArg (fun p : Polynomial (MvPolynomial (Fin n) k) => p.coeff d) heq
    rw [hQconst, Polynomial.coeff_X_pow_self, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, htop, hBcoeff, add_zero] at hx
    exact hx.symm
  have hcinv : (MvPolynomial.C c : MvPolynomial (Fin n) k) * MvPolynomial.C cInv = 1 := by
    rw [← map_mul, hcInv, map_one]
  have hconstant : Q.coeff 0 = MvPolynomial.C cInv := by
    calc
      Q.coeff 0 = Q.coeff 0 * 1 := (mul_one _).symm
      _ = Q.coeff 0 * (MvPolynomial.C c * MvPolynomial.C cInv) := by rw [hcinv]
      _ = MvPolynomial.C cInv := by rw [← mul_assoc, hprodTop, one_mul]
  exact hQconst.trans (congrArg Polynomial.C hconstant)

end PolynomialQuotient

section ConditionalDivision

variable {V : Type*} [CommRing V] [IsLocalRing V]
    (a : V) (ham : a ∈ IsLocalRing.maximalIdeal V) (n d : ℕ)

/-- For a supplied division of `X₀^d` by a divisor with regrouped residue
degree `d` and nonzero scalar top `C c`, whose actual remainder coefficients
vanish at first exponents at least `d`, the quotient residue is `C (c⁻¹)`.
This does not assert existence of a division. -/
theorem restrictedResidueHom_quotient_of_restrictedFinFirst_division
    (f q r : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (c : IsLocalRing.ResidueField V) (hc : c ≠ 0)
    (hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidueHom a ham f)).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidueHom a ham f)).coeff d =
      MvPolynomial.C c)
    (hdivision : polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d) =
      q * f + r)
    (hsupport : ∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
      coeff (β.cons i) (r : MvPowerSeries (Fin (n + 1)) V) = 0) :
    restrictedResidueHom a ham q = MvPolynomial.C (c⁻¹) := by
  let k := V ⧸ IsLocalRing.maximalIdeal V
  let F : Polynomial (MvPolynomial (Fin n) k) :=
    MvPolynomial.finSuccEquiv k n (restrictedResidueHom a ham f)
  let Q : Polynomial (MvPolynomial (Fin n) k) :=
    MvPolynomial.finSuccEquiv k n (restrictedResidueHom a ham q)
  let B : Polynomial (MvPolynomial (Fin n) k) :=
    MvPolynomial.finSuccEquiv k n (restrictedResidueHom a ham r)
  have hB : B.degree < (d : WithBot ℕ) := by
    apply (Polynomial.degree_lt_iff_coeff_zero B d).2
    intro i hi
    apply MvPolynomial.ext
    intro β
    dsimp only [B]
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    rw [coeff_restrictedResidueHom, hsupport i β hi, map_zero]
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  have hX : MvPolynomial.finSuccEquiv k n (restrictedResidueHom a ham
      (polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d))) =
      Polynomial.X ^ d := by
    simpa only [Polynomial.map_pow, Polynomial.map_X] using
      (finSuccEquiv_restrictedResidueHom_polynomialRestrictedFinFirst a ham n
        (Polynomial.X ^ d))
  have heq : Polynomial.X ^ d = Q * F + B := by
    have hres := congrArg (restrictedResidueHom (σ := Fin (n + 1)) a ham) hdivision
    have hfin := congrArg (MvPolynomial.finSuccEquiv k n) hres
    simpa only [hX, map_mul, map_add, F, Q, B] using hfin
  have hcInv : (c : k) * (c⁻¹ : IsLocalRing.ResidueField V) = 1 := by
    exact mul_inv_cancel₀ hc
  have hQ : Q = Polynomial.C (MvPolynomial.C (c⁻¹ : IsLocalRing.ResidueField V)) :=
    quotient_eq_constant_of_scalar_top n d F Q B c
      (c⁻¹ : IsLocalRing.ResidueField V) hc hcInv hdegree htop hB heq
  have hCgen (x : k) : MvPolynomial.finSuccEquiv k n (MvPolynomial.C x) =
      Polynomial.C (MvPolynomial.C x) := by
    simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply]
  have hC : MvPolynomial.finSuccEquiv k n
      (MvPolynomial.C (c⁻¹ : IsLocalRing.ResidueField V)) =
      Polynomial.C (MvPolynomial.C (c⁻¹ : IsLocalRing.ResidueField V)) :=
    hCgen (c⁻¹ : IsLocalRing.ResidueField V)
  apply (MvPolynomial.finSuccEquiv k n).injective
  change Q = MvPolynomial.finSuccEquiv k n
    (MvPolynomial.C (c⁻¹ : IsLocalRing.ResidueField V))
  rw [hC]
  exact hQ

variable (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal V)
    [IsAdicComplete (Ideal.span {a}) V]

include hrad
/-- For a supplied division of `X₀^d` with regrouped divisor residue degree
`d`, nonzero scalar top and actual remainder support below `d`, radical
equality and adic completeness make the quotient a restricted-subring unit.
No positivity restriction applies to `d` or the number of remaining variables. -/
theorem isUnit_quotient_of_restrictedFinFirst_divisionHom
    (f q r : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (c : IsLocalRing.ResidueField V) (hc : c ≠ 0)
    (hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidueHom a ham f)).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidueHom a ham f)).coeff d =
      MvPolynomial.C c)
    (hdivision : polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d) =
      q * f + r)
    (hsupport : ∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
      coeff (β.cons i) (r : MvPowerSeries (Fin (n + 1)) V) = 0) :
    IsUnit q := by
  have hres := restrictedResidueHom_quotient_of_restrictedFinFirst_division a ham
    n d f q r c hc hdegree htop hdivision hsupport
  apply isUnit_of_isUnit_restrictedResidueHom a ham hrad q
  rw [hres]
  exact (isUnit_iff_ne_zero.mpr (inv_ne_zero hc)).map MvPolynomial.C

end ConditionalDivision

section ValuationConditionalDivision

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    (a : V) (ham : a ∈ IsLocalRing.maximalIdeal V)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal V)
    (n d : ℕ)

/-- A supplied division of `X₀^d` with regrouped divisor residue degree `d`,
nonzero scalar top and actual remainder support below `d` determines the
genuine valuation residue `C (c⁻¹)` of the quotient. -/
theorem restrictedResidue_quotient_of_restrictedFinFirst_division
    (f q r : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (c : IsLocalRing.ResidueField V) (hc : c ≠ 0)
    (hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).coeff d =
      MvPolynomial.C c)
    (hdivision : polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d) =
      q * f + r)
    (hsupport : ∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
      coeff (β.cons i) (r : MvPowerSeries (Fin (n + 1)) V) = 0) :
    restrictedResidue a ham q = MvPolynomial.C (c⁻¹) := by
  simpa only [restrictedResidueHom_apply] using
    (restrictedResidueHom_quotient_of_restrictedFinFirst_division a ham n d
      f q r c hc
      (by simpa only [restrictedResidueHom_apply] using hdegree)
      (by simpa only [restrictedResidueHom_apply] using htop)
      hdivision hsupport)

variable [IsAdicComplete (Ideal.span {a}) V]

include hrad
/-- The valuation-domain form of the local-ring unit theorem for a supplied
division of `X₀^d` with matching regrouped divisor residue degree, nonzero
scalar top and actual remainder support below `d`. -/
theorem isUnit_quotient_of_restrictedFinFirst_division
    (f q r : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (c : IsLocalRing.ResidueField V) (hc : c ≠ 0)
    (hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).coeff d =
      MvPolynomial.C c)
    (hdivision : polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d) =
      q * f + r)
    (hsupport : ∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
      coeff (β.cons i) (r : MvPowerSeries (Fin (n + 1)) V) = 0) :
    IsUnit q := by
  apply isUnit_quotient_of_restrictedFinFirst_divisionHom a ham n d hrad f q r c hc
  · simpa only [restrictedResidueHom_apply] using hdegree
  · simpa only [restrictedResidueHom_apply] using htop
  · exact hdivision
  · exact hsupport

end ValuationConditionalDivision

end MvPowerSeries
