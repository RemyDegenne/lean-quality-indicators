noncomputable section

open IsLocalRing

namespace AlgebraicCurve

open scoped Pointwise

section Functoriality

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace SemilinearAut

variable (S : Finset (Place K F × Place K F))

def IsNodeStable (g : SemilinearAut K F) : Prop :=
  ∀ s ∈ S, (g • s.1, g • s.2) ∈ S

end SemilinearAut
end Functoriality
end AlgebraicCurve
end
