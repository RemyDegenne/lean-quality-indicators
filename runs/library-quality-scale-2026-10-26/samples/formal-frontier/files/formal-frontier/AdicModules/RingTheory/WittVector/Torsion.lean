/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import AdicModules.RingTheory.WittVector
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Regular.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Integer torsion in Witt vectors

For prime `p` and a commutative coefficient ring of characteristic `p`, the canonical
integer module of Witt vectors is torsion-free exactly when the coefficient ring is
reduced. This includes reduced rings with zero divisors, without perfectness.

Prime regularity controls multiplication by `p`; every other prime is a unit, detected
on the constant coefficient. Mathlib's finite-additive-order criterion then rules out
all integer torsion.

## References

* Mathlib's `Algebra/Module/Torsion/Free.lean` (Yaël Dillies) for
  `Module.IsTorsionFree` and its integer-module formulation.
* Mathlib's `GroupTheory/OrderOfElement.lean` (Johannes Hölzl and Julian Kuelshammer)
  for finite-order criteria and extraction of elements of prime order.
* Mathlib's `Algebra/CharP/Invertible.lean` (Anne Baanen) for units among integer
  casts, and `RingTheory/WittVector/Basic.lean` (Johan Commelin and Robert Y. Lewis)
  for the constant-coefficient ring homomorphism.
* `AdicModules.RingTheory.WittVector` for the prime-regularity, reducedness and unit
  criteria for Witt vectors.
-/

@[expose] public section

universe u

namespace WittVector

/-- Over a commutative ring of characteristic `p`, the canonical integer module of
`p`-typical Witt vectors is torsion-free exactly when the coefficient ring is reduced. -/
theorem isTorsionFree_int_iff_isReduced
    {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] :
    Module.IsTorsionFree ℤ (WittVector p R) ↔ IsReduced R := by
  constructor
  · intro htf
    apply (isRegular_p_iff_isReduced (p := p) (k := R)).mp
    exact isRegular_natCast.mpr
      (isAddTorsionFree_iff'.mp
        (Module.isTorsionFree_int_iff_isAddTorsionFree.mp htf) p
        (Fact.out : p.Prime).ne_zero)
  · intro hred
    apply Module.isTorsionFree_int_iff_isAddTorsionFree.mpr
    have hprime : ∀ q : ℕ, q.Prime → IsSMulRegular (WittVector p R) q := by
      intro q hq
      apply isRegular_natCast.mp
      by_cases hqp : q = p
      · subst q
        exact (isRegular_p_iff_isReduced (p := p) (k := R)).mpr hred
      · apply IsUnit.isRegular
        apply (isUnit_iff_isUnit_coeff_zero (q : WittVector p R)).mpr
        have hcoeff : (q : WittVector p R).coeff 0 = (q : R) :=
          map_natCast (constantCoeff (p := p) (R := R)) q
        rw [hcoeff]
        apply (CharP.isUnit_natCast_iff (R := R) (Fact.out : p.Prime)).mpr
        intro hdiv
        exact hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).mp hdiv).symm
    -- A nonzero finite-order element has a nonzero multiple of prime order.
    apply IsAddTorsionFree.of_not_isOfFinAddOrder
    intro x hx hfin
    have horder_ne_one : addOrderOf x ≠ 1 := by
      intro horder
      exact hx (AddMonoid.addOrderOf_eq_one_iff.mp horder)
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd horder_ne_one
    letI : Fact q.Prime := ⟨hq⟩
    have horder : addOrderOf ((addOrderOf x / q) • x) = q :=
      orderOf_pow_orderOf_div (x := Multiplicative.ofAdd x)
        hfin.addOrderOf_pos.ne' hqdvd
    obtain ⟨hkill, hne⟩ := addOrderOf_eq_prime_iff.mp horder
    exact hne (hprime q hq (by simpa only [smul_zero] using hkill))

end WittVector
