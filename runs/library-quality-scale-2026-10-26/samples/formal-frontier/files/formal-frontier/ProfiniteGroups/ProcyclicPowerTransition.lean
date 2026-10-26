/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicPowerIndex

/-!
# Maps between procyclic power quotients

Divisibility of exponents gives inclusion of power-image subgroups and a
continuous quotient homomorphism, without assuming either exponent is positive
or either quotient has its exponent as index. The maps preserve quotient
classes, compose, and are surjective.

When the source quotient has index equal to a positive exponent, the target
also has exact index. The equivalences normalized by one topological generator
identify the quotient map with reduction of residue classes.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (torsion-free residue reductions; general quotient-transition laws are developed
  here).
- Mathlib, quotient-group and `ZMod` maps used by `ProcyclicPowerIndex` (power quotients
  and normalized residue reductions).
-/

@[expose] public section

universe u

namespace ProfiniteGrp

/-- Divisibility of exponents reverses inclusion of power-image subgroups. -/
theorem powerImage_le_of_dvd (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    {d n : ℕ} (hdn : d ∣ n) :
    (powerImage G hG n : Subgroup G) ≤ (powerImage G hG d : Subgroup G) := by
  obtain ⟨k, rfl⟩ := hdn
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_powerImage_iff G hG _ x).mp hx
  apply (mem_powerImage_iff G hG _ _).mpr
  refine ⟨y ^ k, ?_⟩
  rw [← pow_mul, mul_comm]

/-- The continuous quotient homomorphism from `n`-th-power classes to
`d`-th-power classes when `d ∣ n`. -/
def powerImage_quotientMap (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    {d n : ℕ} (hdn : d ∣ n) :
    (G ⧸ (powerImage G hG n : Subgroup G)) →ₜ*
      (G ⧸ (powerImage G hG d : Subgroup G)) := by
  let f := QuotientGroup.map (powerImage G hG n : Subgroup G)
    (powerImage G hG d : Subgroup G) (MonoidHom.id G)
    (by
      intro x hx
      exact powerImage_le_of_dvd G hG hdn hx)
  refine ⟨f, ?_⟩
  apply (QuotientGroup.isQuotientMap_mk (powerImage G hG n : Subgroup G)).continuous_iff.mpr
  change Continuous (fun x : G => f (QuotientGroup.mk' _ x))
  have heq : (fun x : G => f (QuotientGroup.mk' _ x)) =
      (fun x : G => QuotientGroup.mk' (powerImage G hG d : Subgroup G) x) := by
    funext x
    simp only [f, QuotientGroup.mk'_apply, QuotientGroup.map_mk,
      MonoidHom.id_apply]
  rw [heq]
  exact QuotientGroup.continuous_mk

/-- A transition map sends a quotient class to the same class at the
coarser power level. -/
theorem powerImage_quotientMap_apply_mk (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) {d n : ℕ} (hdn : d ∣ n) (x : G) :
    powerImage_quotientMap G hG hdn
        (QuotientGroup.mk' (powerImage G hG n : Subgroup G) x) =
      QuotientGroup.mk' (powerImage G hG d : Subgroup G) x := by
  change QuotientGroup.map (powerImage G hG n : Subgroup G)
    (powerImage G hG d : Subgroup G) (MonoidHom.id G)
      (by intro y hy; exact powerImage_le_of_dvd G hG hdn hy)
      (QuotientGroup.mk' (powerImage G hG n : Subgroup G) x) = _
  simpa only [QuotientGroup.mk'_apply, MonoidHom.id_apply] using
    (QuotientGroup.map_mk' (powerImage G hG n : Subgroup G)
      (powerImage G hG d : Subgroup G) (MonoidHom.id G)
      (by intro y hy; exact powerImage_le_of_dvd G hG hdn hy) x)

/-- The quotient transition preserves canonical quotient coercions. -/
@[simp] theorem powerImage_quotientMap_mk (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) {d n : ℕ} (hdn : d ∣ n) (x : G) :
    powerImage_quotientMap G hG hdn
        (x : G ⧸ (powerImage G hG n : Subgroup G)) =
      (x : G ⧸ (powerImage G hG d : Subgroup G)) := by
  simpa only [QuotientGroup.mk'_apply] using
    powerImage_quotientMap_apply_mk G hG hdn x

/-- Transition at the same power level is the identity. -/
@[simp] theorem powerImage_quotientMap_id (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (n : ℕ) :
    powerImage_quotientMap G hG (dvd_refl n) = ContinuousMonoidHom.id _ := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (powerImage G hG n : Subgroup G) q
  simp

/-- Power-quotient transitions compose along a divisibility chain. -/
@[simp] theorem powerImage_quotientMap_comp (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) {e d n : ℕ} (hed : e ∣ d) (hdn : d ∣ n) :
    (powerImage_quotientMap G hG hed).comp (powerImage_quotientMap G hG hdn) =
      powerImage_quotientMap G hG (dvd_trans hed hdn) := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (powerImage G hG n : Subgroup G) q
  simp

/-- Every power-quotient transition is surjective, even if the indices
are smaller than their exponents. -/
theorem powerImage_quotientMap_surjective (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) {d n : ℕ} (hdn : d ∣ n) :
    Function.Surjective (powerImage_quotientMap G hG hdn) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (powerImage G hG d : Subgroup G) q
  exact ⟨QuotientGroup.mk' (powerImage G hG n : Subgroup G) x,
    powerImage_quotientMap_apply_mk G hG hdn x⟩

/-- Exact index at a positive power level descends to its positive divisors. -/
theorem powerImage_index_eq_of_dvd (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) {d n : ℕ} (hdn : d ∣ n) (hn : 0 < n)
    (hindex : (powerImage G hG n : Subgroup G).index = n) :
    (powerImage G hG d : Subgroup G).index = d := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  apply (powerImage_index_eq_iff_exponents G hG d hd).mpr
  have hbound := (powerImage_index_eq_iff_exponents G hG n hn).mp hindex
  intro p
  exact (Nat.cast_le.mpr
    ((Nat.factorization_prime_le_iff_dvd hd.ne' hn.ne').mpr hdn p.1 p.2)).trans
      (hbound p)

/-- The quotient transition agrees with reduction of `ZMod n` to `ZMod d`
under the equivalences fixed by the same topological generator. -/
@[simp] theorem powerImage_quotientMap_zmod (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    {d n : ℕ} (hdn : d ∣ n) (hn : 0 < n)
    (hindex : (powerImage G hG n : Subgroup G).index = n)
    (a : ZMod n) :
    powerImage_quotientMap G hG hdn
        (powerImage_zmodContinuousMulEquiv G hG g hg n hn hindex
          (Multiplicative.ofAdd a)) =
      powerImage_zmodContinuousMulEquiv G hG g hg d
        (Nat.pos_of_dvd_of_pos hdn hn)
        (powerImage_index_eq_of_dvd G hG hdn hn hindex)
        (Multiplicative.ofAdd (ZMod.castHom hdn (ZMod d) a)) := by
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective a
  have hsource : Multiplicative.ofAdd (k : ZMod n) =
      (Multiplicative.ofAdd (1 : ZMod n)) ^ k := by
    simp only [← ofAdd_nsmul, nsmul_one]
  have htarget : Multiplicative.ofAdd (k : ZMod d) =
      (Multiplicative.ofAdd (1 : ZMod d)) ^ k := by
    simp only [← ofAdd_nsmul, nsmul_one]
  rw [hsource, map_pow, powerImage_zmodContinuousMulEquiv_apply_one,
    map_pow, powerImage_quotientMap_apply_mk, map_natCast, htarget,
    map_pow, powerImage_zmodContinuousMulEquiv_apply_one]

end ProfiniteGrp
