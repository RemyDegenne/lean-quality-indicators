public section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry

/-- The small Zariski topology on schemes locally of finite type over a field. -/
noncomputable abbrev lftZariskiTopology (K : Type u) [Field K] :
    GrothendieckTopology (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))) :=
  Scheme.smallGrothendieckTopology (P := openImmersionMorphism)
    (Q := locallyFiniteTypeMorphism) (Spec (.of K))

end AlgebraicGeometry
end
