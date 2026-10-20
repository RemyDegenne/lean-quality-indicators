public section

namespace TauCeti

namespace GridLink

variable {α : Sort*}

/-- Define a function on grid links from a function on grid diagrams that is invariant under
cyclic permutations, elementary commutations, and stabilizations.

No separate destabilization hypothesis is needed: invariance under a stabilization supplies
the reverse equality as well. -/
def lift (f : ∀ n, GridDiagram n → α)
    (hrows : ∀ {n} (G : GridDiagram n), f n G = f n (G.relabelRows (finRotate n)))
    (hcolumns : ∀ {n} (G : GridDiagram n), f n G = f n (G.relabelColumns (finRotate n)))
    (hcomm : ∀ {n} {G G' : GridDiagram n}, GridDiagram.IsCommutation G G' →
      f n G = f n G')
    (hstab : ∀ {n} {G : GridDiagram n} {G' : GridDiagram (n + 1)},
      GridDiagram.IsStabilization G G' → f n G = f (n + 1) G') :
    GridLink → α :=
  Quot.lift (fun G => f G.1 G.2) fun G G' h => by
    cases h with
    | cyclicRows h =>
        rcases h with h | h
        · cases h
          exact hrows _
        · cases h
          exact (hrows _).symm
    | cyclicColumns h =>
        rcases h with h | h
        · cases h
          exact hcolumns _
        · cases h
          exact (hcolumns _).symm
    | commutation h => exact hcomm h
    | stabilization h => exact hstab h
    | destabilization h =>
        exact (hstab (GridDiagram.isDestabilization_iff_isStabilization _ _ |>.mp h)).symm

end GridLink
end TauCeti
end
