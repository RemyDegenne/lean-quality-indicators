/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SupernaturalNumbers.Basic

/-!
# Natural numbers as supernatural numbers

This module extends the positive-natural embedding from
`SupernaturalNumbers.Basic` to all natural numbers. The value zero is sent to
the top supernatural number, in accordance with divisibility: every natural
number divides zero, while zero divides only zero.

No coercion is installed, so callers choose this convention explicitly.
-/

@[expose] public section

namespace Supernatural

/-- Bottom has zero exponent at every prime. -/
@[simp]
theorem exponent_bot (p : Nat.Primes) : exponent (⊥ : Supernatural) p = 0 := rfl

/-- Top has infinite exponent at every prime. -/
@[simp]
theorem exponent_top (p : Nat.Primes) : exponent (⊤ : Supernatural) p = ⊤ := rfl

/-- Embed all natural numbers into supernatural numbers, sending zero to top. -/
def ofNat : ℕ → Supernatural
  | 0 => ⊤
  | n + 1 => ofPNat ⟨n + 1, Nat.succ_pos n⟩

/-- Natural zero embeds as top, reflecting that every natural divides zero. -/
@[simp]
theorem ofNat_zero : ofNat 0 = ⊤ := rfl

/-- A positive successor embeds via the positive-natural factorization map. -/
@[simp]
theorem ofNat_succ (n : ℕ) : ofNat (n + 1) = ofPNat ⟨n + 1, Nat.succ_pos n⟩ := rfl

/-- Natural zero has infinite prime exponents; other naturals use factorization. -/
@[simp]
theorem exponent_ofNat (n : ℕ) (p : Nat.Primes) :
    exponent (ofNat n) p = if n = 0 then ⊤ else (n.factorization p.val : ℕ∞) := by
  cases n <;> rfl

/-- Natural one embeds as supernatural one. -/
theorem ofNat_one : ofNat 1 = 1 := by
  exact ofPNat_one

/-- The two embeddings agree on positive naturals. -/
theorem ofPNat_eq_ofNat (n : ℕ+) : ofPNat n = ofNat n.val := by
  obtain ⟨n, hn⟩ := n
  cases n with
  | zero => simp at hn
  | succ n => rfl

/-- An embedded positive natural is never the top supernatural number. -/
@[simp]
theorem ofPNat_ne_top (n : ℕ+) : ofPNat n ≠ (⊤ : Supernatural) := by
  intro h
  have hp := congrArg (fun x : Supernatural ↦ exponent x ⟨2, Nat.prime_two⟩) h
  change (n.val.factorization 2 : ℕ∞) = ⊤ at hp
  exact ENat.natCast_ne_top _ hp

/-- The all-natural embedding preserves products, including factors equal to zero. -/
@[simp]
theorem ofNat_mul (m n : ℕ) : ofNat (m * n) = ofNat m * ofNat n := by
  ext p
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    simp
  simp [exponent_ofNat, hm, hn, Nat.factorization_mul]

/-- The multiplicative embedding of natural numbers into supernatural numbers. -/
def ofNatHom : ℕ →* Supernatural where
  toFun := ofNat
  map_one' := ofNat_one
  map_mul' := ofNat_mul

/-- Embedded naturals are ordered by divisibility, including both zero cases. -/
theorem ofNat_le_ofNat_iff {m n : ℕ} : ofNat m ≤ ofNat n ↔ m ∣ n := by
  cases m with
  | zero =>
      cases n with
      | zero => simp
      | succ n =>
          have hnot : ¬(⊤ : Supernatural) ≤ ofPNat ⟨n + 1, Nat.succ_pos n⟩ := by
            intro h
            exact ofPNat_ne_top _ (top_unique h)
          simp [ofNat, hnot]
  | succ m =>
      cases n with
      | zero => simp
      | succ n =>
          exact (ofPNat_le_ofPNat_iff
            (m := ⟨m + 1, Nat.succ_pos m⟩) (n := ⟨n + 1, Nat.succ_pos n⟩)).trans
              PNat.dvd_iff

/-- The all-natural embedding is injective, also distinguishing zero from positives. -/
theorem ofNat_injective : Function.Injective ofNat := by
  intro m n h
  apply Nat.dvd_antisymm
  · exact ofNat_le_ofNat_iff.mp h.le
  · exact ofNat_le_ofNat_iff.mp h.ge

/-- The all-natural multiplicative homomorphism is injective. -/
theorem ofNatHom_injective : Function.Injective ofNatHom :=
  ofNat_injective

/-- Divisibility of embedded naturals reflects natural divisibility in both orientations. -/
@[simp]
theorem ofNat_dvd_ofNat_iff {m n : ℕ} : ofNat m ∣ ofNat n ↔ m ∣ n := by
  rw [dvd_iff_le, ofNat_le_ofNat_iff]

/-- Every member of a natural-number family divides its supernatural l.c.m. -/
theorem ofNat_dvd_iSup {ι : Sort*} (f : ι → ℕ) (i : ι) :
    ofNat (f i) ∣ ⨆ j, ofNat (f j) :=
  dvd_iff_le.mpr (le_iSup (fun j ↦ ofNat (f j)) i)

/-- The universal property of the supernatural l.c.m. of natural numbers. -/
theorem iSup_ofNat_dvd_iff {ι : Sort*} (f : ι → ℕ) (n : Supernatural) :
    (⨆ i, ofNat (f i)) ∣ n ↔ ∀ i, ofNat (f i) ∣ n := by
  constructor
  · intro h i
    exact dvd_iff_le.mpr ((le_iSup (fun j ↦ ofNat (f j)) i).trans (dvd_iff_le.mp h))
  · intro h
    exact dvd_iff_le.mpr (iSup_le fun i ↦ dvd_iff_le.mp (h i))

/-- The supernatural l.c.m. of an empty `Sort`-indexed natural family is one. -/
theorem iSup_ofNat_of_isEmpty {ι : Sort*} [IsEmpty ι] (f : ι → ℕ) :
    (⨆ i, ofNat (f i)) = 1 := by
  apply le_antisymm
  · exact iSup_le fun i ↦ isEmptyElim i
  · intro p
    exact bot_le

/-- A natural-number family containing zero has top supernatural l.c.m. -/
theorem iSup_ofNat_eq_top_of_eq_zero {ι : Sort*} (f : ι → ℕ) {i : ι}
    (hi : f i = 0) : ⨆ j, ofNat (f j) = ⊤ := by
  apply eq_top_iff.mpr
  rw [← ofNat_zero, ← hi]
  exact le_iSup (fun j ↦ ofNat (f j)) i

end Supernatural
