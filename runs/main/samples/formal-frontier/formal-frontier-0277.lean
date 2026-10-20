@[expose] public section

universe u v w

open CategoryTheory TopRep ContRepresentation

namespace ContinuousCohomology

variable {k : Type u} {G H : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep k G} {Y : TopRep k H}

theorem cocyclesMap_injective (φ : H →ₜ* G) (f : res φ X ⟶ Y)
    (hφ : Function.Surjective φ) (hf : Function.Injective f.hom) (n : ℕ) :
    Function.Injective (cocyclesMap φ f n) := by
  have : Mono ((cochainsMap φ f).f n) :=
    ConcreteCategory.mono_of_injective _ (cochainsMap_injective φ f hφ hf n)
  let : Limits.PreservesLimitsOfShape Limits.WalkingCospan (forget (TopModuleCat k)) := by
    rw [← HasForget₂.forget_comp (C := TopModuleCat k) (D := TopCat)]
    infer_instance
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (cocyclesMap φ f n)

end ContinuousCohomology
end
