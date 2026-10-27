public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace LayerRestriction

variable {small big : NormalLayer G}

variable {a b c : NormalLayer G}

/-- The **ground-level inclusion** of a restriction: raising the ground field from `F` to `E`
enlarges the ground level, `A^U ⊆ A^{U'}`. It is the degree-zero shadow of `cohomologyRes`. -/
def groundInclusion (T : LayerRestriction small big) (F : Formation G) :
    F.level big.ground →ₗ[ℤ] F.level small.ground :=
  Submodule.inclusion (F.level_antitone T.ground_le)

end LayerRestriction
end TauCeti.ClassFieldTheory
end
