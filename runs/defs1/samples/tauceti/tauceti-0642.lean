public section

namespace TauCeti.DynkinType

open RootPairing.GeckConstruction

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (t : DynkinType) (ht : t.Valid)

/-- **The Chevalley generators of the pinned Lie algebra, numbered by Bourbaki node.** This is
Geck's basis, whose nodes are the support of the pinned base, renumbered along
`TauCeti.DynkinType.simpleSupportEquiv`. -/
def lieBasis : LieAlgebra.Basis (Fin t.rank) (t.cartanSubalgebra ht) :=
  (RootPairing.GeckConstruction.basis (t.rationalBase ht)).reindex (t.simpleSupportEquiv ht).symm

end
end TauCeti.DynkinType
end
