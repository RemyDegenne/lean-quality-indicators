@[expose] public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V]

section RoundOracle

variable [Fintype V]

/-- **The one-round covering oracle.**  An invariant `Inv` on pairs (current residual hypergraph,
currently covered set) which

* holds at the start, and
* as long as more than a `β`-fraction of the vertices is still uncovered, can be advanced by ONE
  round: a retained set `R' ⊆ H'` whose round matching covers at least a `c`-fraction of the
  still-uncovered vertices and re-establishes the invariant.

This is the per-round (non-iterated) content of the nibble outer loop. -/
def HasRoundOracle (H : Finset (Finset V)) (c β : ℝ) : Prop :=
  ∃ Inv : Finset (Finset V) → Finset V → Prop,
    Inv H ∅ ∧
    ∀ (H' : Finset (Finset V)) (S : Finset V), Inv H' S →
      β * (Fintype.card V : ℝ) < (Fintype.card V : ℝ) - (S.card : ℝ) →
      ∃ R' : Finset (Finset V), R' ⊆ H' ∧
        Inv (Hypergraph.residual H' R') (S ∪ support (roundMatching R')) ∧
        c * ((Fintype.card V : ℝ) - (S.card : ℝ))
          ≤ ((support (roundMatching R')).card : ℝ)

end RoundOracle
end LeanPool.AsymptoticTrianglePacking.Internal
end
