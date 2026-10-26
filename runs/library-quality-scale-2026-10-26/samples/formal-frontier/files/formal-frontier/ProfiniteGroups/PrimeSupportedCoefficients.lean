/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicPowerIndices
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.Divisible
public import Mathlib.Data.ZMod.Basic

/-!
# Prime-supported divisibility and torsion of additive coefficients

Surjectivity of multiplication by positive integers supported on a set of primes
is compared with surjectivity at each supporting prime. Torsion uses Mathlib's
`Module.IsTorsion'` and `Submodule.torsion'` for the existing submonoid of
prime-supported indices; it does not introduce a second torsion predicate.

The divisibility predicate is specific to this submonoid: `DivisibleBy A ℕ`
requires division by *every* nonzero natural number and provides an explicit
division operation, rather than asserting surjectivity only at selected indices.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (supported divisibility and torsion for additive coefficients, without a group
  action here).
- Mathlib, `Mathlib.Algebra.Module.Torsion.Basic` and `Mathlib.GroupTheory.Divisible`
  (module torsion and divisibility).
-/

@[expose] public section

universe u

namespace AddMonoid

variable (A : Type u) [AddMonoid A]

/-- Every positive integer supported on `S` acts surjectively on `A` by repeated addition.
This abstracts the supported-divisibility condition in Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Ch. I §7, before Proposition (1.7.7), using
Mathlib’s divisibility API. -/
def IsPrimeSupportedDivisible (S : Set Nat.Primes) : Prop :=
  ∀ n : ℕ, n ∈ Nat.primeSupportedIndices S →
    Function.Surjective (fun a : A => n • a)

/-- An elementwise form of prime-supported divisibility. -/
theorem isPrimeSupportedDivisible_iff (S : Set Nat.Primes) :
    IsPrimeSupportedDivisible A S ↔
      ∀ n : ℕ, n ∈ Nat.primeSupportedIndices S → ∀ a : A, ∃ b : A, n • b = a :=
  Iff.rfl

variable {A}

/-- Multiplication by each supported integer is surjective. -/
theorem IsPrimeSupportedDivisible.surjective {S : Set Nat.Primes}
    (hA : IsPrimeSupportedDivisible A S) {n : ℕ}
    (hn : n ∈ Nat.primeSupportedIndices S) :
    Function.Surjective (fun a : A => n • a) :=
  hA n hn

/-- Every element has a preimage under multiplication by a supported integer. -/
theorem IsPrimeSupportedDivisible.exists_nsmul {S : Set Nat.Primes}
    (hA : IsPrimeSupportedDivisible A S) {n : ℕ}
    (hn : n ∈ Nat.primeSupportedIndices S) (a : A) :
    ∃ b : A, n • b = a :=
  hA.surjective hn a

variable (A)

/-- Divisibility at all supported indices is equivalent to divisibility at
each prime in the support. -/
theorem isPrimeSupportedDivisible_iff_primes (S : Set Nat.Primes) :
    IsPrimeSupportedDivisible A S ↔
      ∀ p : Nat.Primes, p ∈ S → Function.Surjective (fun a : A => p.1 • a) := by
  constructor
  · intro hA p hp
    exact hA p.1 ((Nat.prime_mem_primeSupportedIndices_iff p).mpr hp)
  · intro hp n hn
    refine Submonoid.closure_induction (motive := fun m _ =>
      Function.Surjective (fun a : A => m • a)) ?_ ?_ ?_ hn
    · rintro m ⟨p, hmem, rfl⟩
      exact hp p hmem
    · intro a
      exact ⟨a, by simp⟩
    · intro m k hm hk hms hks a
      obtain ⟨b, hb⟩ := hms a
      obtain ⟨c, hc⟩ := hks b
      exact ⟨c, by simpa only [mul_smul, hc] using hb⟩

/-- Enlarging the support strengthens divisibility. -/
theorem IsPrimeSupportedDivisible.mono {S T : Set Nat.Primes} (hST : S ⊆ T)
    (hA : IsPrimeSupportedDivisible A T) : IsPrimeSupportedDivisible A S := by
  intro n hn
  exact hA n (Nat.primeSupportedIndices_mono hST hn)

/-- Mathlib's divisibility by all nonzero naturals implies divisibility at
any chosen prime-supported indices. -/
theorem isPrimeSupportedDivisible_of_divisibleBy [DivisibleBy A ℕ]
    (S : Set Nat.Primes) : IsPrimeSupportedDivisible A S := by
  intro n hn
  exact DivisibleBy.surjective_smul (A := A) (α := ℕ)
    (Nat.mem_primeSupportedIndices_iff.mp hn).1.ne'

/-- For empty support the only index is one, so every additive monoid is divisible. -/
@[simp] theorem isPrimeSupportedDivisible_empty :
    IsPrimeSupportedDivisible A (∅ : Set Nat.Primes) := by
  intro n hn a
  have hn1 : n = 1 := by simpa using hn
  subst n
  exact ⟨a, by simp⟩

/-- Rational coefficients are divisible at every positive prime-supported index. -/
theorem isPrimeSupportedDivisible_rat (S : Set Nat.Primes) :
    IsPrimeSupportedDivisible ℚ S := by
  intro n hn a
  have hn0 : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.mem_primeSupportedIndices_iff.mp hn).1.ne'
  obtain ⟨b, hb⟩ := (DivisibleBy.surjective_smul (A := ℚ) (α := ℤ) hn0) a
  exact ⟨b, by simpa only [natCast_zsmul] using hb⟩

/-- For prime-order cyclic coefficients, supported divisibility excludes
precisely the characteristic prime. -/
theorem isPrimeSupportedDivisible_zmod_prime_iff (p : Nat.Primes)
    (S : Set Nat.Primes) :
    IsPrimeSupportedDivisible (ZMod p.1) S ↔ p ∉ S := by
  rw [isPrimeSupportedDivisible_iff_primes]
  constructor
  · intro h hp
    obtain ⟨b, hb⟩ := h p hp (1 : ZMod p.1)
    have hzero : p.1 • b = 0 := ZModModule.char_nsmul_eq_zero p.1 b
    have hcast : ((1 : ℕ) : ZMod p.1) = 0 := by
      simpa only [Nat.cast_one] using hb.symm.trans hzero
    exact p.2.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 p.1).mp hcast)
  · intro hp q hq a
    have hne : q ≠ p := by
      intro heq
      exact hp (heq ▸ hq)
    have hnot : ¬ p.1 ∣ q.1 := by
      intro hdvd
      exact hne (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).mp hdvd).symm)
    have hcoprime : q.1.Coprime p.1 :=
      ((p.2.coprime_iff_not_dvd).mpr hnot).symm
    let unit := ZMod.unitOfCoprime q.1 hcoprime
    refine ⟨unit.inv * a, ?_⟩
    calc
      q.1 • (unit.inv * a) = unit.val * (unit.inv * a) := by
        simp [unit, nsmul_eq_mul]
      _ = a := by rw [← mul_assoc, unit.val_inv, one_mul]

end AddMonoid

namespace AddCommGroup

/-- Surjectivity at all supported indices is equivalent to full range for the
existing n-smul homomorphism at each index (`nA = A`). -/
theorem isPrimeSupportedDivisible_iff_nsmul_range_eq_top (A : Type u)
    [AddCommGroup A] (S : Set Nat.Primes) :
    AddMonoid.IsPrimeSupportedDivisible A S ↔
      ∀ n : Nat.primeSupportedIndices S,
        (nsmulAddMonoidHom (α := A) n.1).range = ⊤ := by
  constructor
  · intro h n
    exact AddMonoidHom.range_eq_top.mpr (h n.1 n.2)
  · intro h n hn
    exact AddMonoidHom.range_eq_top.mp (h ⟨n, hn⟩)

end AddCommGroup

namespace Module

/-- Every element is killed by some positive integer whose prime divisors lie in `S`. -/
theorem isTorsion'_primeSupportedIndices_iff (A : Type u) [AddCommGroup A]
    (S : Set Nat.Primes) :
    IsTorsion' A (Nat.primeSupportedIndices S) ↔
      ∀ a : A, ∃ n : ℕ, n ∈ Nat.primeSupportedIndices S ∧ n • a = 0 := by
  constructor
  · intro h a
    obtain ⟨n, hn⟩ := h (x := a)
    exact ⟨n.1, n.2, hn⟩
  · intro h a
    obtain ⟨n, hn, hna⟩ := h a
    exact ⟨⟨n, hn⟩, hna⟩

/-- Enlarging the support weakens the requirement for supported torsion. -/
theorem isTorsion'_primeSupportedIndices_mono (A : Type u) [AddCommGroup A]
    {S T : Set Nat.Primes} (hST : S ⊆ T)
    (hA : IsTorsion' A (Nat.primeSupportedIndices S)) :
    IsTorsion' A (Nat.primeSupportedIndices T) := by
  intro a
  obtain ⟨n, hn⟩ := hA (x := a)
  exact ⟨⟨n.1, Nat.primeSupportedIndices_mono hST n.2⟩, hn⟩

/-- With empty support, torsion is equivalent to having at most one element. -/
theorem isTorsion'_primeSupportedIndices_empty_iff (A : Type u) [AddCommGroup A] :
    IsTorsion' A (Nat.primeSupportedIndices (∅ : Set Nat.Primes)) ↔
      Subsingleton A := by
  constructor
  · intro h
    refine ⟨fun a b => ?_⟩
    obtain ⟨n, hn⟩ := h (x := a)
    have hn1 : (n : ℕ) = 1 := by simpa using n.2
    have ha : a = 0 := by
      change n.1 • a = 0 at hn
      simpa [hn1] using hn
    obtain ⟨m, hm⟩ := h (x := b)
    have hm1 : (m : ℕ) = 1 := by simpa using m.2
    have hb : b = 0 := by
      change m.1 • b = 0 at hm
      simpa [hm1] using hm
    exact ha.trans hb.symm
  · intro h a
    exact ⟨1, Subsingleton.elim _ _⟩

/-- A prime-order cyclic group has supported torsion precisely when its prime
belongs to the support. -/
theorem isTorsion'_zmod_prime_iff (p : Nat.Primes) (S : Set Nat.Primes) :
    IsTorsion' (ZMod p.1) (Nat.primeSupportedIndices S) ↔ p ∈ S := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h (x := (1 : ZMod p.1))
    have hdiv : p.1 ∣ n.1 := (ZMod.natCast_eq_zero_iff n.1 p.1).mp (by
      change n.1 • (1 : ZMod p.1) = 0 at hn
      simpa [nsmul_eq_mul] using hn)
    exact (Nat.mem_primeSupportedIndices_iff.mp n.2).2 p hdiv
  · intro hp a
    exact ⟨⟨p.1, (Nat.prime_mem_primeSupportedIndices_iff p).mpr hp⟩,
      ZModModule.char_nsmul_eq_zero p.1 a⟩

end Module

namespace Submodule

/-- Prime-supported torsion is the directed supremum of its n-torsion kernels. -/
theorem torsion'_primeSupportedIndices_eq_iSup_torsionBy
    (A : Type u) [AddCommGroup A] (S : Set Nat.Primes) :
    torsion' ℤ A (Nat.primeSupportedIndices S) =
      ⨆ n : Nat.primeSupportedIndices S, torsionBy ℤ A (n.1 : ℤ) := by
  have hdirected : Directed (· ≤ ·)
      (fun n : Nat.primeSupportedIndices S => torsionBy ℤ A (n.1 : ℤ)) := by
    intro n m
    refine ⟨n * m, ?_, ?_⟩
    · intro a ha
      apply (mem_torsionBy_iff (R := ℤ) (M := A) _ _).mpr
      have hna : n.1 • a = 0 := by simpa [natCast_zsmul] using ha
      change ((n.1 * m.1 : ℕ) : ℤ) • a = 0
      rw [natCast_zsmul, Nat.mul_comm n.1 m.1, mul_smul, hna, smul_zero]
    · intro a ha
      apply (mem_torsionBy_iff (R := ℤ) (M := A) _ _).mpr
      have hma : m.1 • a = 0 := by simpa [natCast_zsmul] using ha
      change ((n.1 * m.1 : ℕ) : ℤ) • a = 0
      rw [natCast_zsmul, mul_smul, hma, smul_zero]
  have : Nonempty (Nat.primeSupportedIndices S) := ⟨1⟩
  ext a
  rw [mem_iSup_of_directed _ hdirected, mem_torsion'_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa only [mem_torsionBy_iff, natCast_zsmul, Submonoid.smul_def] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa only [mem_torsionBy_iff, natCast_zsmul, Submonoid.smul_def] using hn⟩

/-- The torsion submodule is exactly the union of elements annihilated by a
supported index. -/
theorem coe_torsion'_primeSupportedIndices_eq_iUnion
    (A : Type u) [AddCommGroup A] (S : Set Nat.Primes) :
    (torsion' ℤ A (Nat.primeSupportedIndices S) : Set A) =
      ⋃ n : Nat.primeSupportedIndices S, {a : A | n.1 • a = 0} := by
  ext a
  simp only [SetLike.mem_coe, mem_torsion'_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
  rfl

/-- Supported torsion submodules grow with the support. -/
theorem torsion'_primeSupportedIndices_mono (A : Type u) [AddCommGroup A]
    {S T : Set Nat.Primes} (hST : S ⊆ T) :
    torsion' ℤ A (Nat.primeSupportedIndices S) ≤
      torsion' ℤ A (Nat.primeSupportedIndices T) := by
  intro a ha
  obtain ⟨n, hn⟩ := (mem_torsion'_iff (R := ℤ) (M := A)
    (Nat.primeSupportedIndices S) a).mp ha
  exact (mem_torsion'_iff (R := ℤ) (M := A) (Nat.primeSupportedIndices T) a).mpr
    ⟨⟨n.1, Nat.primeSupportedIndices_mono hST n.2⟩, hn⟩

end Submodule
