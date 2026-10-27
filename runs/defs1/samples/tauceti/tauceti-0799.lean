public section

noncomputable section

open CategoryTheory Limits Simplicial TauCeti

open scoped unitInterval Topology Topology.Homotopy

universe w v u

namespace GenLoop

variable {X : Type w} [TopologicalSpace X] {x : X}

/-- The simplicial set of singular simplices of `X`, as the ambient simplicial set of the pair
`(X, {x})`. -/
abbrev pairSSet (x : X) : SSet.{w} :=
  (TopPair.toSSetPair.obj (TopPair.ofSubset ({x} : Set (TopCat.of X)))).right

end GenLoop
end
end
