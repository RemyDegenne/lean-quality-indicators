open Equiv

public section

namespace TauCeti

universe u

namespace BipartiteRibbonGraph

attribute [instance] fintypeE fintypeB fintypeW decidableEqE decidableEqB decidableEqW

variable (Γ : BipartiteRibbonGraph.{u})

namespace Iso

variable {Γ Δ Θ Ξ : BipartiteRibbonGraph}

/-- Composition of ribbon-graph isomorphisms. -/
@[trans]
def trans (f : Γ.Iso Δ) (g : Δ.Iso Θ) : Γ.Iso Θ where
  edge := f.edge.trans g.edge
  black := f.black.trans g.black
  white := f.white.trans g.white
  map_blackEnd x := by rw [Equiv.trans_apply, g.map_blackEnd, f.map_blackEnd, Equiv.trans_apply]
  map_whiteEnd x := by rw [Equiv.trans_apply, g.map_whiteEnd, f.map_whiteEnd, Equiv.trans_apply]
  map_rotB x := by rw [Equiv.trans_apply, f.map_rotB, g.map_rotB, Equiv.trans_apply]
  map_rotW x := by rw [Equiv.trans_apply, f.map_rotW, g.map_rotW, Equiv.trans_apply]

end Iso
end BipartiteRibbonGraph
end TauCeti
end
