@[expose] public section

namespace PrimeMultiset

theorem coeNat_injective : Function.Injective ((↑) : PrimeMultiset → Multiset ℕ) :=
  Multiset.map_injective Nat.Primes.coe_nat_injective

end PrimeMultiset
end
