/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.FinCases
import ToricIdeals.RationalNormalCurve.Augmentation
import ToricIdeals.RationalNormalCurve.ExponentImage
import ToricIdeals.RationalNormalCurve.MapFlatness
public import ToricIdeals.RationalNormalCurve.QuotientMap

/-!
# Flatness and coefficient functionals for Hankel quotient parametrizations

The quotient parametrization acts on the full two-variable polynomial target.
The induced constant coefficient action on the coefficient ring supports an
origin derivative on a two-generated quotient ideal and a linear coefficient
functional on the target. The degree-zero and degree-one cases are related to
the raw parametrization through the quotient projection.
-/

@[expose] public section

noncomputable section

open MvPolynomial TensorProduct

universe u

namespace ToricIdeals.RationalNormalCurve

private abbrev originQuotient (R : Type u) [CommRing R] (n : ℕ) :=
  Source R n ⧸ hankelIdeal R n

private def originEpsilon (R : Type u) [CommRing R] (n : ℕ) :
    originQuotient R n →+* R :=
  MvPolynomial.constantCoeff.comp (quotientMap R n).toRingHom

private local instance (R : Type u) [CommRing R] (n : ℕ) :
    Algebra (originQuotient R n) R := (originEpsilon R n).toAlgebra

/-- The first partial derivative evaluated at the source origin, as an additive map. -/
private def originDerivative (R : Type u) [CommRing R] (n : ℕ) : Source R n →+ R :=
  (MvPolynomial.constantCoeff : Source R n →+* R).toAddMonoidHom.comp
    (MvPolynomial.pderiv (0 : Fin (n + 1)) :
      Derivation R (Source R n) (Source R n)).toLinearMap.toAddMonoidHom

private theorem originDerivative_mul (R : Type u) [CommRing R] (n : ℕ)
    (f g : Source R n) :
    originDerivative R n (f * g) =
      MvPolynomial.constantCoeff f * originDerivative R n g +
        MvPolynomial.constantCoeff g * originDerivative R n f := by
  change MvPolynomial.constantCoeff (MvPolynomial.pderiv (0 : Fin (n + 1)) (f * g)) =
    MvPolynomial.constantCoeff f *
        MvPolynomial.constantCoeff (MvPolynomial.pderiv (0 : Fin (n + 1)) g) +
      MvPolynomial.constantCoeff g *
        MvPolynomial.constantCoeff (MvPolynomial.pderiv (0 : Fin (n + 1)) f)
  rw [Derivation.leibniz]
  simp only [smul_eq_mul, map_add, map_mul]

/-- Both the value and the first derivative vanish on the quadratic Hankel ideal. -/
private theorem originDerivative_vanishes (R : Type u) [CommRing R] (n : ℕ)
    (f : Source R n) (hf : f ∈ hankelIdeal R n) :
    MvPolynomial.constantCoeff f = 0 ∧ originDerivative R n f = 0 := by
  change f ∈ Submodule.span (Source R n) (Set.range (hankelMinor R n)) at hf
  refine Submodule.span_induction
    (p := fun f _ => MvPolynomial.constantCoeff f = 0 ∧ originDerivative R n f = 0)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨p, rfl⟩
    constructor
    · simp [hankelMinor]
    · simp only [hankelMinor, map_sub, originDerivative_mul,
        MvPolynomial.constantCoeff_X, zero_mul, add_zero, sub_self]
  · exact ⟨map_zero _, map_zero _⟩
  · rintro f g _ _ ⟨hf, hdf⟩ ⟨hg, hdg⟩
    constructor <;> simp only [map_add, hf, hg, hdf, hdg, add_zero]
  · rintro r f _ ⟨hf, hdf⟩
    change MvPolynomial.constantCoeff (r * f) = 0 ∧ originDerivative R n (r * f) = 0
    constructor
    · rw [map_mul, hf, mul_zero]
    · rw [originDerivative_mul, hdf, hf, mul_zero, zero_mul, add_zero]

/-- Additive quotient descent reuses the additive quotient underlying an ideal quotient. -/
private def originDerivativeQuotient (R : Type u) [CommRing R] (n : ℕ) :
    originQuotient R n →+ R :=
  QuotientAddGroup.lift (hankelIdeal R n).toAddSubgroup (originDerivative R n)
    (by
      intro f hf
      exact (originDerivative_vanishes R n f hf).2)

private theorem originDerivativeQuotient_mk (R : Type u) [CommRing R] (n : ℕ)
    (f : Source R n) :
    originDerivativeQuotient R n (Ideal.Quotient.mk (hankelIdeal R n) f) =
      originDerivative R n f := rfl

private theorem originDerivativeQuotient_mul (R : Type u) [CommRing R] (n : ℕ)
    (hn : 0 < n) (q r : originQuotient R n) :
    originDerivativeQuotient R n (q * r) =
      originEpsilon R n q * originDerivativeQuotient R n r +
        originEpsilon R n r * originDerivativeQuotient R n q := by
  refine Quotient.inductionOn₂' q r ?_
  intro f g
  change originDerivative R n (f * g) =
    originEpsilon R n (Ideal.Quotient.mk (hankelIdeal R n) f) * originDerivative R n g +
      originEpsilon R n (Ideal.Quotient.mk (hankelIdeal R n) g) * originDerivative R n f
  have hε : originEpsilon R n = (quotientAugmentation R n).toRingHom :=
    constantCoeff_comp_quotientMap R n hn
  simpa only [hε, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    quotientAugmentation_mk] using originDerivative_mul R n f g

private def firstCoordinate (n : ℕ) (hn : 2 ≤ n) : Fin (n + 1) :=
  ⟨1, by omega⟩

private def originA (R : Type u) [CommRing R] (n : ℕ) : originQuotient R n :=
  Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X (0 : Fin (n + 1)))

private def originB (R : Type u) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    originQuotient R n :=
  Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X (firstCoordinate n hn))

private def originIdeal (R : Type u) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    Ideal (originQuotient R n) :=
  Ideal.span {originA R n, originB R n hn}

private def originIa (R : Type u) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    originIdeal R n hn :=
  ⟨originA R n, Ideal.subset_span (by simp)⟩

private def originIb (R : Type u) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    originIdeal R n hn :=
  ⟨originB R n hn, Ideal.subset_span (by simp)⟩

private theorem originIdeal_le_ker (R : Type u) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    originIdeal R n hn ≤ RingHom.ker (originEpsilon R n) := by
  apply Ideal.span_le.mpr
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  apply RingHom.mem_ker.mpr
  have hε : originEpsilon R n = (quotientAugmentation R n).toRingHom :=
    constantCoeff_comp_quotientMap R n (by omega : 0 < n)
  rcases hq with rfl | rfl <;>
    simp only [originA, originB, hε, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      quotientAugmentation_mk, MvPolynomial.constantCoeff_X]

/-- Restricting the origin derivative to the augmentation ideal removes its second Leibniz term. -/
private def originAlpha (R : Type u) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    originIdeal R n hn →ₗ[originQuotient R n] R := by
  exact
    { toFun := fun x => originDerivativeQuotient R n x
      map_add' := fun x y => (originDerivativeQuotient R n).map_add
        (x : originQuotient R n) (y : originQuotient R n)
      map_smul' := by
        intro q x
        change originDerivativeQuotient R n (q * (x : originQuotient R n)) =
          originEpsilon R n q * originDerivativeQuotient R n x
        rw [originDerivativeQuotient_mul R n (by omega : 0 < n)]
        have hx : originEpsilon R n (x : originQuotient R n) = 0 :=
          RingHom.mem_ker.mp (originIdeal_le_ker R n hn x.property)
        rw [hx, zero_mul, add_zero] }

private theorem originAlpha_ia (R : Type u) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    originAlpha R n hn (originIa R n hn) = 1 := by
  change originDerivative R n (MvPolynomial.X (0 : Fin (n + 1))) = 1
  simp [originDerivative]

private theorem originAlpha_ib (R : Type u) [CommRing R] (n : ℕ) (hn : 2 ≤ n) :
    originAlpha R n hn (originIb R n hn) = 0 := by
  change originDerivative R n (MvPolynomial.X (firstCoordinate n hn)) = 0
  have hne : firstCoordinate n hn ≠ (0 : Fin (n + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp [firstCoordinate] at hv
  simp [originDerivative, MvPolynomial.pderiv_X_of_ne hne]


namespace QuotientFlatness

variable (R : Type u) [CommRing R] (n : ℕ)

private abbrev Q := originQuotient R n

private abbrev phi : Q R n →+* Target R :=
  (quotientMap R n).toRingHom

private abbrev epsilon : Q R n →+* R :=
  originEpsilon R n

private local instance : Algebra (Q R n) (Target R) := (phi R n).toAlgebra
private local instance : Module (Q R n) (Target R) :=
  @Algebra.toModule _ _ _ _ (phi R n).toAlgebra

private theorem rncMap_coeff_linear_eq_zero (hn : 2 ≤ n)
    (p : Source R n) (j : Fin 2) :
    (rncMap R n p).coeff (Finsupp.single j 1) = 0 := by
  apply coeff_rncMap_of_not_mem_range
  rintro ⟨d, hd⟩
  have hdiv : n ∣ ((Finsupp.single j 1 : Fin 2 →₀ ℕ) 0 +
      (Finsupp.single j 1 : Fin 2 →₀ ℕ) 1) :=
    (mem_mrange_rncExponent_iff n _).mp ⟨d, hd⟩
  have hdivone : n ∣ 1 := by
    fin_cases j <;> simpa using hdiv
  have hle := Nat.le_of_dvd (by decide : 0 < 1) hdivone
  omega

private theorem quotientMap_coeff_linear_eq_zero (hn : 2 ≤ n)
    (q : Q R n) (j : Fin 2) :
    (phi R n q).coeff (Finsupp.single j 1) = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  change (rncMap R n p).coeff (Finsupp.single j 1) = 0
  exact rncMap_coeff_linear_eq_zero R n hn p j

/-- Coefficient of the second target variable, for the canonical quotient action. -/
private def beta (hn : 2 ≤ n) : Target R →ₗ[Q R n] R where
  toFun p := p.coeff (Finsupp.single (1 : Fin 2) 1)
  map_add' p q := by simp
  map_smul' q p := by
    change (phi R n q * p).coeff (Finsupp.single (1 : Fin 2) 1) =
      epsilon R n q * p.coeff (Finsupp.single (1 : Fin 2) 1)
    have hlinear : ((quotientMap R n) q).coeff (Finsupp.single (1 : Fin 2) 1) = 0 :=
      quotientMap_coeff_linear_eq_zero R n hn q (1 : Fin 2)
    simp [MvPolynomial.coeff_mul, Finsupp.antidiagonal_single,
      Finset.Nat.antidiagonal_succ,
      epsilon, originEpsilon, MvPolynomial.constantCoeff_eq, hlinear]

private theorem beta_X_zero (hn : 2 ≤ n) :
    beta R n hn (MvPolynomial.X (0 : Fin 2)) = 0 := by
  change (MvPolynomial.X (0 : Fin 2) : Target R).coeff
    (Finsupp.single (1 : Fin 2) 1) = 0
  simp [MvPolynomial.coeff_X, Finsupp.single_eq_single_iff]

private theorem beta_X_one (hn : 2 ≤ n) :
    beta R n hn (MvPolynomial.X (1 : Fin 2)) = 1 := by
  change (MvPolynomial.X (1 : Fin 2) : Target R).coeff
    (Finsupp.single (1 : Fin 2) 1) = 1
  simp

private def tensorWitness (hn : 2 ≤ n) :
    originIdeal R n hn ⊗[Q R n] Target R :=
  originIa R n hn ⊗ₜ[Q R n] X 1 - originIb R n hn ⊗ₜ[Q R n] X 0

private def tensorDetector (hn : 2 ≤ n) :
    originIdeal R n hn ⊗[Q R n] Target R →ₗ[Q R n] R :=
  (LinearMap.mul' (Q R n) R).comp
    (TensorProduct.map (originAlpha R n hn) (beta R n hn))

private theorem tensorDetector_witness (hn : 2 ≤ n) :
    tensorDetector R n hn (tensorWitness R n hn) = 1 := by
  simp [tensorDetector, tensorWitness, originAlpha_ia, originAlpha_ib,
    beta_X_zero, beta_X_one]

private theorem quotientMap_coordinate_relation (hn : 2 ≤ n) :
    phi R n (originA R n) * X 1 = phi R n (originB R n hn) * X 0 := by
  have ha : phi R n (originA R n) = (X (0 : Fin 2) : Target R) ^ n := by
    simp [phi, originA, quotientMap_mk, rncMap_X, coordinateExponent,
      X_pow_eq_monomial]
  have hb : phi R n (originB R n hn) =
      (X (0 : Fin 2) : Target R) ^ (n - 1) * X 1 := by
    have hexp : coordinateExponent n (firstCoordinate n hn) =
        Finsupp.single (0 : Fin 2) (n - 1) + Finsupp.single (1 : Fin 2) 1 := by
      ext j
      fin_cases j <;> simp [coordinateExponent, firstCoordinate]
    change quotientMap R n
      (Ideal.Quotient.mk (hankelIdeal R n) (X (firstCoordinate n hn))) = _
    rw [quotientMap_mk, rncMap_X, hexp, X_pow_eq_monomial]
    change (monomial (Finsupp.single (0 : Fin 2) (n - 1) +
      Finsupp.single (1 : Fin 2) 1)) (1 : R) =
        (monomial (Finsupp.single (0 : Fin 2) (n - 1))) 1 *
          (monomial (Finsupp.single (1 : Fin 2) 1)) 1
    rw [monomial_mul_monomial, one_mul]
  have hdegree : n - 1 + 1 = n := by omega
  have hpow := pow_succ (X (0 : Fin 2) : Target R) (n - 1)
  rw [hdegree] at hpow
  rw [ha, hb, hpow]
  exact mul_right_comm _ _ _

private theorem tensorWitness_in_kernel (hn : 2 ≤ n) :
    (originIdeal R n hn).subtype.rTensor (Target R) (tensorWitness R n hn) = 0 := by
  apply (TensorProduct.lid (Q R n) (Target R)).injective
  simp only [tensorWitness, map_sub, map_zero, LinearMap.rTensor_tmul,
    TensorProduct.lid_tmul]
  change phi R n (originA R n) * X 1 - phi R n (originB R n hn) * X 0 = 0
  exact sub_eq_zero.mpr (quotientMap_coordinate_relation R n hn)

private theorem quotientMap_not_flat [Nontrivial R] (hn : 2 ≤ n) :
    ¬ (quotientMap R n).toRingHom.Flat := by
  intro h
  let : Module.Flat (Q R n) (Target R) := h
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := Target R)
    (originIdeal R n hn).subtype Subtype.val_injective
  have hw : tensorWitness R n hn = 0 :=
    hinj (by simpa only [map_zero] using tensorWitness_in_kernel R n hn)
  have hz : (1 : R) = 0 := by
    simpa only [tensorDetector_witness, map_zero] using
      congrArg (tensorDetector R n hn) hw
  exact one_ne_zero hz

end QuotientFlatness

/-- At degree one the full quotient parametrization is flat over every
commutative coefficient ring. -/
private theorem quotientMap_flat_one (R : Type u) [CommRing R] :
    (quotientMap R 1).toRingHom.Flat := by
  have hprojection :
      Function.Bijective (Ideal.Quotient.mk (hankelIdeal R 1)) :=
    (Ideal.Quotient.mk_bijective_iff_eq_bot _).mpr (hankelIdeal_one R)
  let e : Source R 1 ≃+* (Source R 1 ⧸ hankelIdeal R 1) :=
    RingEquiv.ofBijective (Ideal.Quotient.mk (hankelIdeal R 1)) hprojection
  have hinverse : e.symm.toRingHom.Flat :=
    RingHom.Flat.of_bijective e.symm.bijective
  have hraw : (rncMap R 1).Flat :=
    (rncMap_flat_iff R 1).mpr (Or.inl rfl)
  have hcomposition :
      (rncMap R 1).comp e.symm.toRingHom =
        (quotientMap R 1).toRingHom := by
    apply RingHom.ext
    intro q
    change rncMap R 1 (e.symm q) = quotientMap R 1 q
    rw [← quotientMap_mk R 1 (e.symm q)]
    exact congrArg (quotientMap R 1) (e.apply_symm_apply q)
  rw [← hcomposition]
  exact hinverse.comp hraw

/-- Subsingleton coefficients make the full target a flat module for the
canonical quotient-map action, in every degree. -/
private theorem quotientMap_flat_of_subsingleton (R : Type u) [CommRing R]
    [Subsingleton R] (n : ℕ) :
    (quotientMap R n).toRingHom.Flat := by
  let : Algebra (Source R n ⧸ hankelIdeal R n) (Target R) :=
    (quotientMap R n).toRingHom.toAlgebra
  let : Module (Source R n ⧸ hankelIdeal R n) (Target R) :=
    @Algebra.toModule (Source R n ⧸ hankelIdeal R n) (Target R) _ _
      ((quotientMap R n).toRingHom.toAlgebra)
  have hflat :
      (algebraMap (Source R n ⧸ hankelIdeal R n) (Target R)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  simpa only [RingHom.algebraMap_toAlgebra] using hflat

/-- At degree zero the Hankel ideal is zero, so flatness of the quotient
map would imply flatness of the raw map through a bijective projection. -/
private theorem quotientMap_not_flat_zero (R : Type u) [CommRing R]
    [Nontrivial R] :
    ¬ (quotientMap R 0).toRingHom.Flat := by
  intro hflat
  have hprojection : (Ideal.Quotient.mk (hankelIdeal R 0)).Flat :=
    RingHom.Flat.of_bijective
      ((Ideal.Quotient.mk_bijective_iff_eq_bot _).mpr (hankelIdeal_zero R))
  have hraw : (rncMap R 0).Flat := by
    rw [← quotientMap_comp_mk R 0]
    exact hprojection.comp hflat
  rcases (rncMap_flat_iff R 0).mp hraw with hdegree | hsubsingleton
  · exact Nat.zero_ne_one hdegree
  · let : Subsingleton R := hsubsingleton
    exact (zero_ne_one : (0 : R) ≠ 1) (Subsingleton.elim _ _)


/-- The parametrization from the full Hankel quotient to the full bivariate
polynomial ring is flat exactly in degree one or over a zero coefficient ring.
The action is induced by `quotientMap`, not by the coefficient inclusion.

In degree at least two, the origin derivative on a two-generated quotient ideal
and a linear target coefficient detect a nonzero tensor killed by inclusion.
The boundary degrees are compared to the raw parametrization through the
bijective quotient projection. -/
theorem quotientMap_flat_iff (R : Type u) [CommRing R] (n : ℕ) :
    (quotientMap R n).toRingHom.Flat ↔ n = 1 ∨ Subsingleton R := by
  classical
  constructor
  · intro hflat
    by_cases hR : Subsingleton R
    · exact Or.inr hR
    · let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
      by_cases hn : n = 1
      · exact Or.inl hn
      · by_cases hzero : n = 0
        · subst n
          exact False.elim (quotientMap_not_flat_zero R hflat)
        · exact False.elim
            (QuotientFlatness.quotientMap_not_flat R n (by omega) hflat)
  · rintro (hn | hR)
    · subst n
      exact quotientMap_flat_one R
    · let : Subsingleton R := hR
      exact quotientMap_flat_of_subsingleton R n


end ToricIdeals.RationalNormalCurve

end
