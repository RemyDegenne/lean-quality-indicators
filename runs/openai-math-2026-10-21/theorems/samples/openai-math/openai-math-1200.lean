namespace OAI

namespace Ostmann

theorem exists_reduced_class (t : Finset ℕ) (f : ℕ → ℕ) (M : ℕ)
    (ha : ∀ a ∈ t, a ≤ M) (hf : ∀ a ∈ t, f a ≤ M)
    (hne : ∀ a ∈ t, a ≠ f a) :
    ∃ Q r : ℕ, Q ≠ 0 ∧ r.Coprime Q ∧
      ∀ a ∈ t, r ≡ separatingPrime M a + a - f a [MOD separatingPrime M a] ∧
        separatingPrime M a ∣ Q := by
  classical
  let q := separatingPrime M
  let c := fun a => q a + a - f a
  have hq : ∀ a, (q a).Prime := separatingPrime_prime M
  have hnonzero : ∀ a ∈ t, q a ≠ 0 := fun a _ => (hq a).ne_zero
  have hpair : Set.Pairwise (↑t : Set ℕ) (fun a b => (q a).Coprime (q b)) := by
    intro a _ b _ hab
    exact (Nat.coprime_primes (hq a) (hq b)).mpr
      (fun h => hab (separatingPrime_injective M h))
  let r := Nat.chineseRemainderOfFinset c q t hnonzero hpair
  have hr : ∀ a ∈ t, (r : ℕ) ≡ c a [MOD q a] := r.property
  have hc : ∀ a ∈ t, (c a).Coprime (q a) := by
    intro a hat
    exact shifted_difference_coprime (hq a)
      ((ha a hat).trans_lt (lt_separatingPrime M a))
      ((hf a hat).trans_lt (lt_separatingPrime M a)) (hne a hat)
  refine ⟨∏ a ∈ t, q a, r, Finset.prod_ne_zero_iff.mpr hnonzero, ?_, ?_⟩
  · apply Nat.coprime_prod_right_iff.mpr
    intro a hat
    have hmod := hr a hat
    change (r : ℕ) % q a = c a % q a at hmod
    rw [← ZMod.coprime_mod_iff_coprime, hmod, ZMod.coprime_mod_iff_coprime]
    exact hc a hat
  · intro a hat
    exact ⟨hr a hat, Finset.dvd_prod_of_mem q hat⟩

end Ostmann
end OAI
