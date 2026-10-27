public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  {x z : GridState n}

/-- All terminal self-pairs: the common-terminal-side sources and their distinct counted
rectangle--pentagon recuts. -/
noncomputable def terminalSelfPairs (x z : GridState n) :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.terminalSelfPairSources C x z).withPartners
    ⟨G.terminalSelfPairPartner C, G.terminalSelfPairPartner_injective C⟩

end TauCeti.GridDiagram
end
