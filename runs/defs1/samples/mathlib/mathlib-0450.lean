@[expose] public section

universe t w u u' v v'

namespace Rep

open CategoryTheory Finsupp TensorProduct Representation

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {S : Subgroup G}
  [DecidableRel (QuotientGroup.rightRel S)] (A : Rep.{w} k S)

variable {A}

variable [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (A)

variable (k S)

variable {k S}

variable (k S) in
/-- Given a finite index subgroup `S ≤ G`, `Coind_S^G` is left adjoint to the restriction functor
`Res k G ⥤ Res k S`, since it is naturally isomorphic to `Ind_S^G`. -/
noncomputable def coindResAdjunction :
    coindFunctor k S.subtype ⊣ resFunctor.{max w u v} S.subtype :=
  (indResAdjunction k S.subtype).ofNatIsoLeft (indCoindNatIso.{max w u v} k S)

end Rep
end
