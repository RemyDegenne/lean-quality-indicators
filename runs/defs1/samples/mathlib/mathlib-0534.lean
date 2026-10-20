@[expose] public section

open CategoryTheory Opposite

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Profinite

open FiniteGaloisIntermediateField ProfiniteGrp

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

variable (k K)

/-- The categorical isomorphism between `profiniteGalGrp` and `lim Gal(L/k)` where `L` is a
  `FiniteGaloisIntermediateField` ordered by inverse inclusion -/
noncomputable def profiniteGalGrpIsoLimit [IsGalois k K] :
    profiniteGalGrp k K ≅ limit (asProfiniteGaloisGroupFunctor k K) :=
  ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivToLimit k K)

end InfiniteGalois
end Profinite
end
