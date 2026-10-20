set_option warningAsError true

@[expose] public section

noncomputable section

universe uN uE uQ uH

namespace TopologicalAbelianization

variable (G : Type uN) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The canonical homomorphism from algebraic abelianization to topological
abelianization. -/
def fromAbelianization : Abelianization G →* TopologicalAbelianization G :=
  Abelianization.lift
    (QuotientGroup.mk' (commutator G).topologicalClosure)

end TopologicalAbelianization
end
end
