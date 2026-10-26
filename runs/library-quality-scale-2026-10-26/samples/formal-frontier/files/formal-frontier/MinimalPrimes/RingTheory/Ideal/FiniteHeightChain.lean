/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.FiniteHeightChain
public import Mathlib.Order.CompleteLattice.Lemmas
public import Mathlib.Order.OrderIsoNat
public import Mathlib.RingTheory.Ideal.Height

/-!
# Antitone prime chains starting at finite height

An antitone sequence of prime ideals is eventually constant when its initial prime has finite
height. Its intersection equals the ideal at a stabilization index. The corresponding
statement for points of the prime spectrum uses its order by ideal inclusion and applies to
commutative semirings. The ideal statement uses the finite-height API for commutative rings.

Mathlib supplies an `Ideal.FiniteHeight` instance for every ideal of a Noetherian commutative
ring after importing `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`. This class includes the unit
ideal as an exception. Initial primeness excludes that exception, so the instance gives the
numerical bound `(J 0).height < ⊤`. Thus the ideal statement needs no separate height hypothesis
in the Noetherian case. None of the statements requires globally finite Krull dimension, a
domain, or an Artinian ring. In the zero ring there are no prime ideals, so a sequence of primes
cannot exist.

The order-height bound concerns the lower interval in `PrimeSpectrum R`, not the lower interval
in the lattice of all ideals. `Ideal.height` measures prime chains and is not `Order.height`
on that lattice. Every term must be prime: in `k[t]`, the ideals `(tⁿ⁺¹)` form a strictly
descending sequence whose initial ideal is prime of height one, but whose later terms are not
prime.

## References

These statements use Mathlib's `PrimeSpectrum.asIdeal_le_asIdeal`,
`PrimeSpectrum.height_eq_orderHeight`, `Ideal.FiniteHeight`, and
`Ideal.height_lt_top_of_isPrime`. Mathlib's `Ideal.finiteHeight_of_isNoetherianRing`, a consequence
of Krull's height theorem, supplies the Noetherian specialization without another theorem.
The chain and intersection APIs include `WellFoundedLT.antitone_chain_condition` and
`Antitone.iInf_nat_add`.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- A descending sequence of points of the prime spectrum of a commutative semiring stabilizes
if its initial point has finite height. The intersection of the associated ideals is the ideal
at a stabilization index. The order on the prime spectrum is ideal inclusion. -/
theorem exists_stable_of_antitone_of_height_lt_top
    {R : Type u} [CommSemiring R] (P : ℕ → PrimeSpectrum R)
    (hP : Antitone P) (hfin : Order.height (P 0) < ⊤) :
    ∃ N : ℕ, (∀ n : ℕ, N ≤ n → P n = P N) ∧
      (⨅ n, (P n).asIdeal) = (P N).asIdeal := by
  let Q : ℕ → Set.Iic (P 0) := fun n => ⟨P n, hP (Nat.zero_le n)⟩
  let : WellFoundedLT (Set.Iic (P 0)) :=
    Order.wellFoundedLT_Iic_of_height_lt_top (P 0) hfin
  have hQ : Antitone Q := fun _ _ h => hP h
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hQ
  have hstable : ∀ n : ℕ, N ≤ n → P n = P N :=
    fun n hn => congrArg Subtype.val (hN n hn).symm
  refine ⟨N, hstable, le_antisymm (iInf_le _ N) (le_iInf fun n => ?_)⟩
  rcases le_total n N with hn | hn
  · exact (asIdeal_le_asIdeal _ _).mpr (hP hn)
  · exact (congrArg asIdeal (hstable n hn)).symm.le

end PrimeSpectrum

namespace Ideal

/-- An antitone sequence of prime ideals stabilizes if its initial prime has finite height.
Its intersection is the ideal at a stabilization index. `FiniteHeight` is required only for the
initial ideal; primeness rules out the unit-ideal exception in that class. -/
theorem exists_stable_of_antitone_of_finiteHeight
    {R : Type u} [CommRing R] (J : ℕ → Ideal R)
    (hJ : Antitone J) (hprime : ∀ n, (J n).IsPrime) [(J 0).FiniteHeight] :
    ∃ N : ℕ, (∀ n : ℕ, N ≤ n → J n = J N) ∧ (⨅ n, J n) = J N := by
  let P : ℕ → PrimeSpectrum R := fun n => ⟨J n, hprime n⟩
  have hP : Antitone P := fun _ _ h => (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (hJ h)
  have hfin : Order.height (P 0) < ⊤ := by
    rw [← PrimeSpectrum.height_eq_orderHeight]
    let : (J 0).IsPrime := hprime 0
    exact Ideal.height_lt_top_of_isPrime (I := J 0)
  obtain ⟨N, hN, hInf⟩ :=
    PrimeSpectrum.exists_stable_of_antitone_of_height_lt_top P hP hfin
  exact ⟨N, fun n hn => congrArg PrimeSpectrum.asIdeal (hN n hn), hInf⟩

end Ideal
