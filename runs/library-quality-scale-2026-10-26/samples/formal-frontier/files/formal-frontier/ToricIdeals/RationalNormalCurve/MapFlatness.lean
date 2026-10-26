/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.RationalNormalCurve
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Fin.SuccPred
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness of the rational-normal-curve parametrization

For every commutative coefficient ring and every degree, `rncMap R n` is flat
exactly when the degree is one or the coefficient ring is subsingleton.
Flatness concerns the full bivariate polynomial target as a module over the
full source via this ring homomorphism: `p • q = rncMap R n p * q`.
It is not coefficient-module flatness of the target or of the Hankel quotient.

At degree one the exponent identity identifies the map with the identity.
Subsingleton coefficients make the full target trivial. In the other degrees,
`X₀ - 1` or `X₁² - X₀ X₂` is a regular source scalar with zero image. Selecting
one variable exhibits each relation as a monic polynomial over an arbitrary
coefficient ring. On a flat module such a scalar must act injectively, which
contradicts its annihilation of the target's nonzero unit.

The theorem expresses genuine commutative-ring flatness. Mathlib's broader
semiring `Module.Flat` expresses tensor-monomorphism preservation; no
classification of that semiring property is asserted here.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the
  parametrization, exponent identity, and vanishing of the Hankel minors.
* Mathlib contributors, `Mathlib.RingTheory.RingHom.Flat` and
  `Mathlib.RingTheory.Flat.TorsionFree`, for flat ring maps and preservation
  of regular scalar actions on flat modules.
* Mathlib contributors, `Mathlib.Algebra.Polynomial.Monic`,
  `Mathlib.Algebra.MvPolynomial.Equiv`, and `Mathlib.Algebra.Regular.SMul`,
  for monic regularity, variable selection, and equivalence transport.

The classification is an original composition of these polynomial and
flatness results, without a domain or Noetherian hypothesis.
-/

@[expose] public section

open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

universe u

private theorem rncMap_one_eq_id (R : Type u) [CommRing R] :
    rncMap R 1 = RingHom.id (Target R) := by
  have hexponent : rncExponent 1 = AddMonoidHom.id (Fin 2 →₀ ℕ) := by
    apply AddMonoidHom.ext
    exact rncExponent_one
  rw [rncMap, hexponent, AddMonoidAlgebra.mapDomainRingHom_id]

private theorem degree_zero_regular_relation (R : Type u) [CommRing R] :
    IsRegular (X (0 : Fin 1) - C 1 : Source R 0) ∧
      rncMap R 0 (X (0 : Fin 1) - C 1) = 0 := by
  constructor
  · let p : Source R 0 := X 0 - C 1
    let e := MvPolynomial.finSuccEquiv R 0
    have hregular : IsRegular (e p) := by
      simpa [p, e, MvPolynomial.finSuccEquiv_X_zero] using
        (Polynomial.monic_X_sub_C (1 : MvPolynomial (Fin 0) R)).isRegular
    have hleft : IsLeftRegular p :=
      (Equiv.isSMulRegular_congr (e := e.toEquiv) (r := p) (s := e p)
        (fun q => e.map_mul p q)).mpr hregular.left
    exact ⟨hleft, hleft.right_of_commute (fun q => mul_comm p q)⟩
  · simp [rncMap_X, coordinateExponent]

private theorem quadratic_regular_relation (R : Type u) [CommRing R] (m : ℕ) :
    IsRegular (X (1 : Fin (m + 3)) ^ 2 - X 0 * X 2 : Source R (m + 2)) ∧
      rncMap R (m + 2) (X (1 : Fin (m + 3)) ^ 2 - X 0 * X 2) = 0 := by
  constructor
  · let p : Source R (m + 2) := X 1 ^ 2 - X 0 * X 2
    let e := (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin (m + 3)) 1)).trans
      (MvPolynomial.finSuccEquiv R (m + 2))
    have hx0 : e (X (0 : Fin (m + 3))) = Polynomial.C (X (0 : Fin (m + 2))) := by
      simpa only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X, Equiv.swap_apply_left, Fin.succ_zero_eq_one'] using
        (MvPolynomial.finSuccEquiv_X_succ (R := R) (j := (0 : Fin (m + 2))))
    have hx1 : e (X (1 : Fin (m + 3))) = Polynomial.X := by
      simp only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X, Equiv.swap_apply_right, MvPolynomial.finSuccEquiv_X_zero]
    have htwo : (2 : Fin (m + 3)).val = 2 := by
      change 2 % (m + 3) = 2
      exact Nat.mod_eq_of_lt (by omega)
    have hswap : Equiv.swap (0 : Fin (m + 3)) 1 2 = 2 := by
      apply Equiv.swap_apply_of_ne_of_ne
      · apply Fin.ne_of_val_ne
        simpa only [htwo, Fin.val_zero] using (by decide : (2 : ℕ) ≠ 0)
      · apply Fin.ne_of_val_ne
        simpa only [htwo, Fin.val_one] using (by decide : (2 : ℕ) ≠ 1)
    have hx2 : e (X (2 : Fin (m + 3))) = Polynomial.C (X (1 : Fin (m + 2))) := by
      simpa only [e, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X, hswap, Fin.succ_one_eq_two'] using
        (MvPolynomial.finSuccEquiv_X_succ (R := R) (j := (1 : Fin (m + 2))))
    have he : e p = Polynomial.X ^ 2 -
        Polynomial.C (X (0 : Fin (m + 2)) * X 1 : MvPolynomial (Fin (m + 2)) R) := by
      simp only [p, map_sub, map_pow, map_mul, hx0, hx1, hx2]
    have hregular : IsRegular (e p) := by
      rw [he]
      exact (Polynomial.monic_X_pow_sub_C _ (by decide : (2 : ℕ) ≠ 0)).isRegular
    have hleft : IsLeftRegular p :=
      (Equiv.isSMulRegular_congr (e := e.toEquiv) (r := p) (s := e p)
        (fun q => e.map_mul p q)).mpr hregular.left
    exact ⟨hleft, hleft.right_of_commute (fun q => mul_comm p q)⟩
  · let index : MinorIndex (m + 2) := ⟨(0, 1), Fin.one_pos'⟩
    have hcast1 : (1 : Fin (m + 2)).castSucc = (1 : Fin (m + 3)) := by
      apply Fin.ext
      simp
    have hminor : hankelMinor R (m + 2) index =
        (X 0 * X 2 - X 1 ^ 2 : Source R (m + 2)) := by
      simp only [hankelMinor, index, Fin.castSucc_zero', hcast1,
        Fin.succ_zero_eq_one', Fin.succ_one_eq_two', pow_two]
    have hzero : rncMap R (m + 2) (hankelMinor R (m + 2) index) = 0 :=
      (hankelIdeal_le_ker R (m + 2)) (minor_mem R (m + 2) index)
    have hneg : (X 1 ^ 2 - X 0 * X 2 : Source R (m + 2)) =
        -hankelMinor R (m + 2) index := by
      rw [hminor, neg_sub]
    rw [hneg, map_neg, hzero, neg_zero]

/-- The rational-normal-curve ring homomorphism is flat exactly in degree one
or over a subsingleton coefficient ring. This is flatness of the full
`MvPolynomial (Fin 2) R` as a module over the full
`MvPolynomial (Fin (n + 1)) R` via `(rncMap R n).toAlgebra`, in every universe
and every degree, including zero. No domain, Noetherianity, nontriviality or
positive-degree hypothesis is required. The proof uses Mathlib's monic
regularity and regular-scalar preservation on flat modules. -/
theorem rncMap_flat_iff (R : Type u) [CommRing R] (n : ℕ) :
    (rncMap R n).Flat ↔ n = 1 ∨ Subsingleton R := by
  constructor
  · intro hflat
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · let : Nontrivial R := hR
      left
      by_contra hn
      have hrelation : ∃ p : Source R n, IsRegular p ∧ rncMap R n p = 0 := by
        cases n with
        | zero => exact ⟨_, degree_zero_regular_relation R⟩
        | succ n =>
          cases n with
          | zero => exact (hn rfl).elim
          | succ m => exact ⟨_, quadratic_regular_relation R m⟩
      obtain ⟨p, hregular, hzero⟩ := hrelation
      let : Algebra (Source R n) (Target R) := (rncMap R n).toAlgebra
      let : Module (Source R n) (Target R) :=
        @Algebra.toModule (Source R n) (Target R) _ _ ((rncMap R n).toAlgebra)
      let : Module.Flat (Source R n) (Target R) :=
        RingHom.flat_algebraMap_iff.mp
          (by simpa only [RingHom.algebraMap_toAlgebra] using hflat)
      have hscalar : IsSMulRegular (Target R) p :=
        Module.Flat.isSMulRegular_of_isRegular hregular
      have hkill : p • (1 : Target R) = 0 := by
        rw [RingHom.smul_toAlgebra (rncMap R n), hzero, zero_mul]
      exact one_ne_zero (hscalar.right_eq_zero_of_smul hkill)
  · rintro (rfl | hR)
    · rw [rncMap_one_eq_id]
      exact RingHom.Flat.id (Target R)
    · let : Subsingleton R := hR
      let : Algebra (Source R n) (Target R) := (rncMap R n).toAlgebra
      let : Module (Source R n) (Target R) :=
        @Algebra.toModule (Source R n) (Target R) _ _ ((rncMap R n).toAlgebra)
      have hflat : (algebraMap (Source R n) (Target R)).Flat :=
        RingHom.flat_algebraMap_iff.mpr inferInstance
      simpa only [RingHom.algebraMap_toAlgebra] using hflat

end

end ToricIdeals.RationalNormalCurve
