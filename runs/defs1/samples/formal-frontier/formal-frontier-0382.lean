public section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry

local instance (K : Type u) [Field K] : (lftAffineInclusion K).Full :=
  (lftAffineInclusionFullyFaithful K).full

local instance (K : Type u) [Field K] : (lftAffineInclusion K).Faithful :=
  (lftAffineInclusionFullyFaithful K).faithful

local instance lftOver_locallyCoverDense
    (K : Type u) [Field K] :
    (MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K))).LocallyCoverDense
      (Scheme.overGrothendieckTopology openImmersionMorphism (Spec (.of K))) :=
  Scheme.locallyCoverDense_of_le (Spec (.of K))
    openImmersionMorphism_le_locallyFiniteTypeMorphism

local instance lftOver_representablyFlat
    (K : Type u) [Field K] :
    RepresentablyFlat
      (MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K))) :=
  flat_of_preservesFiniteLimits _

local instance lftOver_isContinuous
    (K : Type u) [Field K] :
    (MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K))).IsContinuous
      (lftZariskiTopology K)
      (Scheme.overGrothendieckTopology openImmersionMorphism (Spec (.of K))) := by
  rw [Functor.isContinuous_iff_coverPreserving]
  exact Functor.coverPreserving_restrictedTopology
    (MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K)))
    (Scheme.overGrothendieckTopology openImmersionMorphism (Spec (.of K)))

local instance lftZariskiTopology_subcanonical
    (K : Type u) [Field K] : (lftZariskiTopology K).Subcanonical := by
  change ((MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤
    (Spec (.of K))).restrictedTopology
    (Scheme.overGrothendieckTopology openImmersionMorphism (Spec (.of K)))).Subcanonical
  apply GrothendieckTopology.subcanonical_of_full_of_faithful
    (MorphismProperty.Over.forget locallyFiniteTypeMorphism ⊤ (Spec (.of K)))
    (lftZariskiTopology K)
    (Scheme.overGrothendieckTopology openImmersionMorphism (Spec (.of K)))

/-- Finitely generated algebras over a field, oppositely, are equivalent to affine
locally-finite-type schemes over that field. -/
noncomputable def fgAlgCatOpEquivLftAffineOver
    (K : Type u) [Field K] : (FGAlgCat K)ᵒᵖ ≌ lftAffineOver K := by
  let _ : (fgAlgToLftAffine K).Full :=
    (fgAlgToLftAffineFullyFaithful K).full
  let _ : (fgAlgToLftAffine K).Faithful :=
    (fgAlgToLftAffineFullyFaithful K).faithful
  let _ : (fgAlgToLftAffine K).EssSurj := fgAlgToLftAffineEssSurj K
  let _ : (fgAlgToLftAffine K).IsEquivalence := {}
  exact (fgAlgToLftAffine K).asEquivalence

end AlgebraicGeometry
end
