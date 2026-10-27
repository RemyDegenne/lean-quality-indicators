public section

namespace TauCeti.Huber

open TauCeti.Localization

open scoped Uniformity

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (T : Finset A) (s t : A)
  (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

section OneStep

variable (T' : Finset A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
  (hden' : HasDenominatorPower P T' s S') (hTT' : ∀ u ∈ T, u ∈ T')

/-- **Wedhorn's Remark 7.55**: when the numerators of `T'` are those of `T` together with `t`, the
Laurent quotient *is* `A⟨T'/s⟩`,

```text
A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)  ≃  A⟨T'/s⟩
```

the two maps already constructed being mutually inverse. This is the identification Proposition
8.30 consumes: it turns a statement about the Laurent quotient, such as its flatness over
`A⟨T/s⟩`, into the same statement about `A⟨T'/s⟩`.

Use `TauCeti.Huber.PairOfDefinition.continuous_laurentQuotientRingEquiv` and its `symm` form for
continuity, and the `@[simp]` lemmas below to compute: the equivalence is
`TauCeti.Huber.PairOfDefinition.laurentQuotientRestrictionRingHom` and its inverse is
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom`. -/
noncomputable def laurentQuotientRingEquiv (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) ≃+* UniformSpace.Completion S' :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_locUniformSpace P T s S hden
  letI := locUniformSpace P T' s S' hden'
  letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
  letI := isTopologicalRing_locUniformSpace P T' s S' hden'
  letI := isHuberRing_locUniformSpace P T' s S' hden'
  RingEquiv.ofRingHom (laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht)
    (laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl)
    (laurentQuotientRestrictionRingHom_comp_laurentQuotientRingHom P T s t S hden T' S' hden'
      hTT' ht hsplit hcl)
    (laurentQuotientRingHom_comp_laurentQuotientRestrictionRingHom P T s t S hden T' S' hden'
      hTT' ht hsplit hcl)

end OneStep
end PairOfDefinition
end TauCeti.Huber
end
