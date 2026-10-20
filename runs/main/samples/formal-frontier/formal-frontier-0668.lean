@[expose] public section

universe u v w

open CategoryTheory TopRep ContRepresentation

namespace ContinuousCohomology

variable {k : Type u} {G H : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep k G} {Y : TopRep k H}

theorem resolutionMap_injective (φ : H →ₜ* G) (f : res φ X ⟶ Y)
    (hφ : Function.Surjective φ) (hf : Function.Injective f.hom) (i : ℕ) :
    Function.Injective (resolutionMap φ f i).hom := by
  induction i with
  | zero => exact hf
  | succ i hi =>
    intro a b hab
    apply ContinuousMap.ext
    intro g
    obtain ⟨h, rfl⟩ := hφ g
    apply hi
    have heval := congrArg (fun F => F h) hab
    simpa only [resolutionMap_succ, TopRep.hom_ofHom, coind₁ResMap_apply] using heval

end ContinuousCohomology
end
