set_option warningAsError true

@[expose] public section

open CategoryTheory HomogeneousIdeal

open AlgebraicGeometry

namespace ProjectiveSpace

universe u uA uB uσ uτ

section UniverseMonomorphic

variable {A B σ τ : Type u}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]

variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A scheme isomorphism induces an equivalence on closed points. -/
noncomputable def closedPointsEquivOfIso
    {X Y : Scheme.{u}} (e : X ≅ Y) : closedPoints X ≃ closedPoints Y :=
  (Scheme.homeoOfIso e).toEquiv.subtypeEquiv fun x ↦ by
    rw [mem_closedPoints_iff, mem_closedPoints_iff]
    change IsClosed {x} ↔ IsClosed {(Scheme.homeoOfIso e) x}
    simpa only [Set.image_singleton] using
      ((Scheme.homeoOfIso e).isClosed_image (s := {x})).symm

end UniverseMonomorphic
end ProjectiveSpace
end
