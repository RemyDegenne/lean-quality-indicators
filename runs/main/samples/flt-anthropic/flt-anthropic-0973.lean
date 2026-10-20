namespace P2MW.S_UniqueFactorizationMonoid_of_isLocalization_away_of_prime

set_option autoImplicit false

namespace P2mNagata

open IsLocalization

variable {R : Type*} [CommRing R] [IsDomain R]

variable {x : R} (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S]

lemma prime_of_prime_algebraMap (hx : Prime x) {r₀ : R} (hr₀ : ¬x ∣ r₀) (hunit : ¬IsUnit r₀)
    (hprime : Prime (algebraMap R S r₀)) : Prime r₀ := by
  have hinj := algebraMap_injective S hx.ne_zero
  refine ⟨fun h => hprime.ne_zero (by rw [h, map_zero]), hunit, fun a b hab => ?_⟩

  have key : ∀ a : R, algebraMap R S r₀ ∣ algebraMap R S a → r₀ ∣ a := by
    intro a ⟨d, hd⟩
    obtain ⟨c, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers x) d
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : R) x).mp s.2

    have h1 : algebraMap R S (a * x ^ n) = algebraMap R S (r₀ * c) := by
      rw [map_mul, map_mul, hd, hn, mul_assoc, IsLocalization.mk'_spec]
    have h2 : a * x ^ n = r₀ * c := hinj h1
    have h3 : x ^ n ∣ r₀ * c := ⟨a, by rw [← h2, mul_comm]⟩
    obtain ⟨c', rfl⟩ := pow_dvd_of_pow_dvd_mul_left hx hr₀ n c h3
    refine ⟨c', mul_right_cancel₀ (pow_ne_zero n hx.ne_zero) ?_⟩
    rw [h2]; ring
  have : algebraMap R S r₀ ∣ algebraMap R S a * algebraMap R S b := by
    rw [← map_mul]; exact map_dvd (algebraMap R S) hab
  rcases hprime.dvd_or_dvd this with h | h
  · exact Or.inl (key a h)
  · exact Or.inr (key b h)

end P2mNagata
end P2MW.S_UniqueFactorizationMonoid_of_isLocalization_away_of_prime
