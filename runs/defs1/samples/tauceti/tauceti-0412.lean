public section

namespace Ideal

open _root_.IsDedekindDomain

variable {R : Type*} [CommRing R]

/-- An ideal of a Dedekind domain is **prime to** a set `S` of height-one primes when it is
nonzero and no prime of `S` divides it. Nonzeroness is part of the definition, so `⊥` is prime
to no set at all — not even to `∅`. -/
def IsPrimeTo (I : Ideal R) (S : Set (HeightOneSpectrum R)) : Prop :=
  I ≠ ⊥ ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I

end Ideal
end
