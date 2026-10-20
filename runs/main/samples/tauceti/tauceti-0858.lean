public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace LayerRestriction

variable {small big : NormalLayer G}

variable {a b c : NormalLayer G}

theorem cohomologyRes_def (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.cohomologyRes F n = groupCohomology.map T.galHom (T.repIso F).inv n := (rfl)

end LayerRestriction
end TauCeti.ClassFieldTheory
end
