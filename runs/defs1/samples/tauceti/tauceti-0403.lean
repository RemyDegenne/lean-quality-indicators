public section

open Matrix

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*}

/-- The blow-up of a plumbing graph along an edge `_h : P.toSimpleGraph.Adj u v`: adjoin a new
exceptional vertex `none` with framing `-1`, connect it to `some u` and `some v`, remove the direct
edge between `some u` and `some v`, and decrease the framings of `some u` and `some v` by one. -/
def blowUpEdge [DecidableEq V] (P : PlumbingGraph V) (u v : V) (_h : P.toSimpleGraph.Adj u v) :
    PlumbingGraph (Option V) where
  toSimpleGraph :=
    { Adj := P.BlowUpEdgeAdj u v
      symm := P.blowUpEdgeAdj_symm u v
      loopless := P.blowUpEdgeAdj_irrefl u v }
  decidableAdj := P.decidableBlowUpEdgeAdj u v
  weight a := a.elim (-1) fun w => if w = u ∨ w = v then P.weight w - 1 else P.weight w

end PlumbingGraph
end TauCeti
end
