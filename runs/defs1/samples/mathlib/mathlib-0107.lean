@[expose] public section

namespace PrimeMultiset

/-- If a `List ℕ+` consists only of primes, it can be recast as a `PrimeMultiset` with
the coercion from lists to multisets. -/
def ofPNatList (l : List ℕ+) (h : ∀ p : ℕ+, p ∈ l → p.Prime) : PrimeMultiset :=
  ofPNatMultiset (l : Multiset ℕ+) h

end PrimeMultiset
end
