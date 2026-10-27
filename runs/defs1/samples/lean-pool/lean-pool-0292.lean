@[expose] public section

namespace AtanasovRanganathan

open Utilities

open Certificate

open Certificate.ExplicitPotential

open Certificate.SubdivisionGraph

/-- The finite geometric genus-five boundary produced by the public
pseudocore normal form.  Each input is a valid loop-aware pseudocore with at
most eight base vertices; the obligation is uniform over every positive
subdivision of its checked loopless split.

This formulation deliberately does not mention the historical numbering of
the sixteen cubic pictures.  A finite catalog theorem may discharge these
quantifiers later, while structural proofs can already handle looped,
separated, and small-core families directly. -/
def GenusFivePseudocorePencils : Prop :=
  ∀ (vertexCount : ℕ)
    (core : Certificate.GenusFourPseudocore.Pseudocore vertexCount)
    (split : core.SplitMetadata),
    vertexCount ≤ 8 →
    core.ValidAt 5 →
    Certificate.PseudocoreSplitGlue.Compatible split →
    ∀ spec : Spec (vertexCount + core.loopCount) core.splitEdgeCount,
      spec.core = split.splitCore → BNExists spec.graph 1 4

end AtanasovRanganathan
end
