public section

namespace TauCeti.Huber

open TauCeti.Localization

namespace PairOfDefinition

section Identification

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] [CompleteSpace A] (P : PairOfDefinition A) (T : Set A) (s : A) (S : Type*)
  [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  {k : ℕ} (t : Fin k → A) (ht : ∀ i, t i ∈ T) (hsplit : ∀ u ∈ T, u = s ∨ u ∈ Set.range t)
  (hspan : Ideal.span (insert s T) = ⊤)
  (hcl : IsClosed (rationalRelationIdeal t s : Set (weightedRestrictedSubring
    (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)))

include hsplit hspan hcl

include ht

/-- **The presentation map `A⟨X₁, …, Xₖ⟩ → A⟨T/s⟩`**: the quotient map by the relation ideal
`(tᵢ - s Xᵢ)` followed by `rationalQuotientRingEquiv`. It exhibits the completed rational
localisation as a quotient of a restricted power-series ring in one stroke, which is what a
caller wanting generators and relations for `A⟨T/s⟩` needs: it is surjective
(`rationalQuotientHom_surjective`) and continuous (`continuous_rationalQuotientHom`), sends a
constant to its image under the structure map (`rationalQuotientHom_weightedC`), takes the
relations to zero (`rationalQuotientHom_weightedC_mul_weightedX`), and has the relation ideal for
its kernel (`rationalQuotientHom_eq_zero_iff_mem`). Its hypotheses are those of
`rationalQuotientRingEquiv`. -/
noncomputable def rationalQuotientHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      UniformSpace.Completion S :=
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  (rationalQuotientRingEquiv P T s S hden t ht hsplit hspan hcl).toRingHom.comp
    (Ideal.Quotient.mk _)

end Identification
end PairOfDefinition
end TauCeti.Huber
end
