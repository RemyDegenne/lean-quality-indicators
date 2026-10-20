@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

theorem mono_iff_injective_spec {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mono f ↔ ∀ (R : Type u) [CommRing R],
      Function.Injective (fun g : Spec (.of R) ⟶ X ↦ g ≫ f) := by
  rw [isSeparating_isAffine.mono_iff f]
  constructor
  · intro H R _ g h e
    exact H _ inferInstance g h e
  · intro H T hT g h e
    letI := hT
    apply (cancel_epi T.isoSpec.inv).mp
    apply H Γ(T, ⊤)
    simpa only [Category.assoc] using congrArg (fun k ↦ T.isoSpec.inv ≫ k) e

end AlgebraicGeometry.Scheme
end
