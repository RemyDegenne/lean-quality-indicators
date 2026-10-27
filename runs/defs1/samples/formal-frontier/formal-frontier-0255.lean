public section

set_option autoImplicit false

set_option warningAsError true

open CategoryTheory

noncomputable section

namespace ContinuousGroupCohomology

universe u

variable (R G : Type u) [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

namespace RestrictedLevelCompactRep

variable {R G}

variable {A B C : RestrictedLevelCompactRep R G}

/-- Coefficient maps give natural transformations of the actual norm diagrams. -/
@[expose] def restrictedNormDiagramMap (f : A ⟶ B) :
    restrictedNormDiagram A ⟶ restrictedNormDiagram B where
  app U := groupMap f U
  naturality {V U} hVU := groupMap_relativeNorm f U V (leOfHom hVU)

end RestrictedLevelCompactRep
end ContinuousGroupCohomology
end
end
