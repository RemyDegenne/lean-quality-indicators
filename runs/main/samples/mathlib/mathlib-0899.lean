@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

variable (K : Precoverage Scheme.{u})

variable {K}

variable {X Y Z : Scheme.{u}} (𝒰 : X.Cover K) (f : X ⟶ Z) (g : Y ⟶ Z)

variable [∀ x, HasPullback (𝒰.f x ≫ f) g]

lemma Cover.covers [JointlySurjective K] (𝒰 : X.Cover K) (x : X) :
    x ∈ Set.range (𝒰.f (𝒰.idx x)) :=
  (𝒰.exists_eq x).choose_spec

end Scheme
end AlgebraicGeometry
end
end
