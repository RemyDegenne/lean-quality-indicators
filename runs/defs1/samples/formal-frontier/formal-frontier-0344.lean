@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The metric two-sphere with both poles removed is homotopy equivalent to its
equator subtype through the displayed projection, inclusion, and deformation. -/
noncomputable def sphere2PunctureIntersectionEquatorHomotopyEquiv :
    sphere2PunctureIntersection ≃ₕ sphere2Equator where
  toFun := sphere2PunctureIntersectionToEquator
  invFun := sphere2EquatorToPunctureIntersection
  left_inv := ⟨sphere2PunctureIntersectionRadialHomotopy⟩
  right_inv := by
    have h : sphere2PunctureIntersectionToEquator.comp
        sphere2EquatorToPunctureIntersection =
        ContinuousMap.id sphere2Equator := by
      apply ContinuousMap.ext
      intro p
      exact sphere2PunctureIntersectionToEquator_inclusion p
    exact h ▸ ContinuousMap.Homotopic.refl _

end SphereTopology
end
end
