public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} {G G' : GridDiagram n}

theorem IsCommutation.componentCount_eq (h : IsCommutation G G') :
    G'.componentCount = G.componentCount := by
  rw [componentCount_def, h.componentCycleType_eq, componentCount_def]

end GridDiagram
end TauCeti
end
