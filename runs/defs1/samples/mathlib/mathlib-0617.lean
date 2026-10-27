@[expose] public section

noncomputable section

open FaithfulSMul Function Set Submodule

open List hiding mem_toFinset

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

namespace RootPairing

namespace EmbeddedG2

variable [P.EmbeddedG2]

/-- The index of the root `3α + β` where `α` is the short root and `β` is the long root. -/
def threeShortAddLong : ι := P.reflectionPerm (short P) (long P)

end EmbeddedG2
end RootPairing
end
end
