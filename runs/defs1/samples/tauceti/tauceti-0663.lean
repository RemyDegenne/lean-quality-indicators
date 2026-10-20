public section

open CategoryTheory

namespace TauCeti

universe u₁ u₂ v₁ v₂ w

open GradedLinearQuiver

variable {R : Type w} [CommRing R] {C : Type u₁} {D : Type u₂}
  [GradedLinearQuiver.{u₁, v₁, w} R C] [GradedLinearQuiver.{u₂, v₂, w} R D]

namespace AInfinityFunctor

variable {ℬ : AInfinityCategory R C} {𝒞 : AInfinityCategory R D} (ℱ : AInfinityFunctor ℬ 𝒞)

variable (hℬ : ℬ.CohomologicallyUnital) (h𝒞 : 𝒞.CohomologicallyUnital) {ℱ}

variable (hℱ : ℱ.IsUnital)

/-- `H⁰` of the identity `A∞` functor is the identity functor. -/
noncomputable def mapHomotopyCategoryIdIso :
    mapHomotopyCategory hℬ hℬ (isUnital_id (ℬ := ℬ)) ≅ 𝟭 (AInfinityHomotopyCategory ℬ hℬ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {X Y} a ↦ by
    obtain ⟨f, hf, rfl⟩ := ℬ.exists_homClass_eq a
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    -- The identity functor acts on Hom modules by the identity, hence on classes too.
    rw [mapHomotopyCategory_map, homClassMap_homClass, Functor.id_map]
    simp only [id_map_apply]
    -- The two classes now differ only in the object `(AInfinityFunctor.id ℬ).obj X.obj`, which
    -- is `X.obj` by definition (`AInfinityFunctor.id_obj`).
    rfl

end AInfinityFunctor
end TauCeti
end
