/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENat.SuccOrder
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Supernatural numbers

A supernatural number is a prime-indexed family of exponents in `ℕ∞`.  We use
the multiplicative type tag so that multiplication of supernatural numbers is
pointwise addition of exponents.

The natural-number interface initially uses positive naturals.  In particular,
it does not identify `0` with `1` through the convention
`Nat.factorization 0 = 0`.
-/

@[expose] public section

/-- A supernatural number, represented by its exponent at every prime. -/
abbrev Supernatural := Multiplicative (Nat.Primes → ℕ∞)

namespace Supernatural

/-- The exponent of a prime in a supernatural number. -/
def exponent (n : Supernatural) (p : Nat.Primes) : ℕ∞ :=
  Multiplicative.toAdd n p

/-- Supernatural numbers are equal when their exponents agree at every prime. -/
@[ext]
theorem ext {m n : Supernatural} (h : ∀ p, exponent m p = exponent n p) : m = n :=
  Multiplicative.toAdd.injective (funext h)

attribute [inherit_doc Supernatural.ext] Supernatural.ext_iff

/-- The exponent of one is zero at every prime. -/
@[simp]
theorem exponent_one (p : Nat.Primes) : exponent 1 p = 0 := rfl

/-- Multiplication adds exponents at each prime. -/
@[simp]
theorem exponent_mul (m n : Supernatural) (p : Nat.Primes) :
    exponent (m * n) p = exponent m p + exponent n p := rfl

/-- Taking a natural power scales each prime exponent. -/
@[simp]
theorem exponent_pow (n : Supernatural) (k : ℕ) (p : Nat.Primes) :
    exponent (n ^ k) p = k • exponent n p := by
  rfl

noncomputable instance : CompleteLattice Supernatural :=
  Multiplicative.toAdd.completeLattice

/-- The least supernatural number has zero exponent at every prime, so it is one. -/
@[simp]
theorem bot_eq_one : (@Bot.bot Supernatural instCompleteLattice.toBot) = 1 := by
  apply le_antisymm
  · exact bot_le
  · intro p
    exact bot_le

/-- Suprema of arbitrary `Sort`-indexed families are computed primewise. -/
@[simp]
theorem exponent_iSup {ι : Sort*} (f : ι → Supernatural) (p : Nat.Primes) :
    exponent (⨆ i, f i) p = ⨆ i, exponent (f i) p := by
  apply le_antisymm
  · have h : (⨆ i, f i) ≤ Multiplicative.ofAdd (fun q ↦ ⨆ i, exponent (f i) q) := by
      refine iSup_le fun i ↦ ?_
      intro q
      exact le_iSup (fun j ↦ exponent (f j) q) i
    exact h p
  · refine iSup_le fun i ↦ ?_
    exact (le_iSup f i) p

/-- Infima of arbitrary `Sort`-indexed families are computed primewise. -/
@[simp]
theorem exponent_iInf {ι : Sort*} (f : ι → Supernatural) (p : Nat.Primes) :
    exponent (⨅ i, f i) p = ⨅ i, exponent (f i) p := by
  apply le_antisymm
  · refine le_iInf fun i ↦ ?_
    exact (iInf_le f i) p
  · have h : Multiplicative.ofAdd (fun q ↦ ⨅ i, exponent (f i) q) ≤ ⨅ i, f i := by
      refine le_iInf fun i ↦ ?_
      intro q
      exact iInf_le (fun j ↦ exponent (f j) q) i
    exact h p

/-- The exponent of a finite product is the sum of its prime exponents. -/
@[simp]
theorem exponent_prod {ι : Type*} (s : Finset ι) (f : ι → Supernatural)
    (p : Nat.Primes) :
    exponent (∏ i ∈ s, f i) p = ∑ i ∈ s, exponent (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- The product of an arbitrary family of supernatural numbers.

At each prime, its exponent is the supremum of the sums over finite
subfamilies. -/
noncomputable def iProd {ι : Type*} (f : ι → Supernatural) : Supernatural :=
  Multiplicative.ofAdd fun p ↦ ⨆ s : Finset ι, ∑ i ∈ s, exponent (f i) p

/-- An arbitrary product has the supremum of all finite-subfamily exponent sums. -/
@[simp]
theorem exponent_iProd {ι : Type*} (f : ι → Supernatural) (p : Nat.Primes) :
    exponent (iProd f) p = ⨆ s : Finset ι, ∑ i ∈ s, exponent (f i) p := rfl

/-- For a finite index type, the arbitrary product agrees with the finite product. -/
theorem iProd_eq_prod {ι : Type*} [Fintype ι] (f : ι → Supernatural) :
    iProd f = ∏ i, f i := by
  classical
  ext p
  rw [exponent_iProd, exponent_prod]
  apply le_antisymm
  · exact iSup_le fun s ↦ Finset.sum_le_sum_of_subset (Finset.subset_univ s)
  · exact le_iSup_of_le Finset.univ le_rfl

/-- A factor with infinite exponent forces an infinite exponent in the product. -/
theorem exponent_iProd_eq_top_of_eq_top {ι : Type*} (f : ι → Supernatural)
    (p : Nat.Primes) {i : ι} (hi : exponent (f i) p = ⊤) :
    exponent (iProd f) p = ⊤ := by
  classical
  apply top_unique
  rw [exponent_iProd]
  refine le_iSup_of_le {i} ?_
  simp [hi]

/-- Infinitely many factors with nonzero exponent force an infinite product exponent. -/
theorem exponent_iProd_eq_top_of_infinite_support {ι : Type*}
    (f : ι → Supernatural) (p : Nat.Primes)
    (h : Set.Infinite {i | exponent (f i) p ≠ 0}) :
    exponent (iProd f) p = ⊤ := by
  rw [exponent_iProd]
  apply top_unique
  rw [← ENat.iSup_natCast]
  refine iSup_le fun n ↦ ?_
  obtain ⟨s, hs, hcard⟩ := h.exists_subset_card_eq n
  refine le_iSup_of_le s ?_
  calc
    (n : ℕ∞) = ∑ _i ∈ s, (1 : ℕ∞) := by simp [hcard]
    _ ≤ ∑ i ∈ s, exponent (f i) p :=
      Finset.sum_le_sum fun i hi ↦ Order.one_le_iff_ne_zero.mpr (hs hi)

/-- The supernatural number associated to a positive natural number. -/
def ofPNat (n : ℕ+) : Supernatural :=
  Multiplicative.ofAdd fun p ↦ (n.val.factorization p.val : ℕ∞)

/-- The prime exponent of an embedded positive natural is its factorization exponent. -/
@[simp]
theorem exponent_ofPNat (n : ℕ+) (p : Nat.Primes) :
    exponent (ofPNat n) p = (n.val.factorization p.val : ℕ∞) := rfl

/-- Positive natural one embeds as supernatural one. -/
@[simp]
theorem ofPNat_one : ofPNat 1 = 1 := by
  ext p
  simp [ofPNat, exponent]

/-- The positive-natural embedding preserves multiplication. -/
@[simp]
theorem ofPNat_mul (m n : ℕ+) : ofPNat (m * n) = ofPNat m * ofPNat n := by
  ext p
  simp [ofPNat, exponent, PNat.mul_coe, Nat.factorization_mul m.pos.ne' n.pos.ne']

/-- Embedding positive naturals into supernatural numbers. -/
def ofPNatHom : ℕ+ →* Supernatural where
  toFun := ofPNat
  map_one' := ofPNat_one
  map_mul' := ofPNat_mul

/-- Distinct positive naturals have distinct supernatural prime exponents. -/
theorem ofPNat_injective : Function.Injective ofPNat := by
  intro m n h
  apply PNat.eq
  apply Nat.eq_of_factorization_eq m.pos.ne' n.pos.ne'
  intro p
  by_cases hp : p.Prime
  · have hp' := congrArg (fun x : Supernatural ↦ Multiplicative.toAdd x ⟨p, hp⟩) h
    change (m.val.factorization p : ℕ∞) = (n.val.factorization p : ℕ∞) at hp'
    exact ENat.natCast_inj.mp hp'
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The positive-natural multiplicative homomorphism is injective. -/
theorem ofPNatHom_injective : Function.Injective ofPNatHom :=
  ofPNat_injective

/-- Exponentwise order of embedded positive naturals reflects divisibility. -/
theorem ofPNat_le_ofPNat_iff {m n : ℕ+} : ofPNat m ≤ ofPNat n ↔ m ∣ n := by
  rw [PNat.dvd_iff, ← Nat.factorization_prime_le_iff_dvd m.pos.ne' n.pos.ne']
  constructor
  · intro h
    change (∀ p : Nat.Primes,
      (m.val.factorization p.val : ℕ∞) ≤ (n.val.factorization p.val : ℕ∞)) at h
    intro p hp
    exact ENat.natCast_le_natCast.mp (h ⟨p, hp⟩)
  · intro h
    change ∀ p : Nat.Primes,
      (m.val.factorization p.val : ℕ∞) ≤ (n.val.factorization p.val : ℕ∞)
    intro p
    exact ENat.natCast_le_natCast.mpr (h p.val p.prop)

/-- Divisibility of supernatural numbers is exactly exponentwise order. -/
theorem dvd_iff_le {m n : Supernatural} : m ∣ n ↔ m ≤ n := by
  constructor
  · rintro ⟨c, rfl⟩ p
    exact self_le_add_right _ _
  · exact exists_mul_of_le

end Supernatural
