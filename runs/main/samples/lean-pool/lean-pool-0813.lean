@[expose] public section

namespace Model

variable {K : Type u} [CommRing K]

variable [IsDomain K]

namespace Field

variable {K : Type u} [Field K]

open ECTate ECTate.PerfectRing

lemma ringChar_eq_of_Prime [Nat.AtLeastTwo n] (hn : @OfNat.ofNat K n _ = 0) (hnp : Nat.Prime n) :
  ringChar K = n := by
  rw [← Nat.cast_ofNat, ringChar.spec] at hn
  cases (Nat.dvd_prime hnp).mp hn with
  | inl h =>
    have hh := CharP.char_is_prime_or_zero K (ringChar K)
    rw [h] at hh
    exact absurd hh (by simp [Nat.not_prime_one])
  | inr h =>
    assumption

end Field
end Model
end
