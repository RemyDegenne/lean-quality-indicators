@[expose] public section

variable {ι α β γ : Type*}

namespace Finset

open Multiset

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

section gcd

/-- Greatest common divisor of a finite set -/
def gcd (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.gcd 0 f

end gcd
end Finset
end
