public section

open scoped TensorProduct

namespace TauCeti

universe u v w

variable (R : Type u) (C : Type v)

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace Subcoalgebra

variable {R C}

section Domain

variable {S : Type u} {D : Type v} [CommRing S] [IsDomain S] [AddCommGroup D] [Module S D]

variable [Module.IsTorsionFree S D] [Coalgebra S D]

/-- Over a domain, the group-like elements of a torsion-free coalgebra that they span form a
basis of it. -/
noncomputable def groupLikeBasis (h : groupLikeSetSpan (R := S) (C := D) Set.univ = ⊤) :
    Module.Basis (GroupLike S D) S D :=
  Module.Basis.mk linearIndep_groupLikeVal
    ((groupLikeSetSpan_eq_top_iff_span_eq_top (R := S) (C := D)).mp h).ge

end Domain
end Subcoalgebra
end TauCeti
end
