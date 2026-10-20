@[expose] public section

open IsLocalRing

namespace ValuationSubring

universe u

variable {K : Type u} [Field K]

@[simp]
theorem ofPrime_compositeIdeal (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) :
    (A.composite W).ofPrime (A.compositeIdeal W) = A :=
  (A.composite W).ofPrime_idealOfLE A (A.composite_le W)

end ValuationSubring
end
