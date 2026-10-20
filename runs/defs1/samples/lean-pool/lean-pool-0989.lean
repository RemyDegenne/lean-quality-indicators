@[expose] public section

namespace ErdosProblems.MulticolourTriangleRamsey

open Filter Finset SimpleGraph

open scoped Topology

/-- Data certifying that a blockwise edge coloring contains no monochromatic triangle. -/
structure PaletteBlockCertificate {I V K : Type*} [DecidableEq K]
    (C : SimpleGraph.TopEdgeLabeling (I × V) K) (j : ℕ) where
  /-- The colors omitted from internal edges of each block. -/
  palette : I → Finset K
  /-- A proper internal vertex coloring for every active color in a block. -/
  label : ∀ (i : I) (colour : K), colour ∉ palette i → V → Fin j
  internal_no_triangle :
    ∀ (i : I) (colour : K) (u v w : V),
      ¬ ((C.labelGraph colour).Adj (i, u) (i, v) ∧
         (C.labelGraph colour).Adj (i, u) (i, w) ∧
         (C.labelGraph colour).Adj (i, v) (i, w))
  missing_has_no_internal_edge :
    ∀ (i : I) (colour : K), colour ∈ palette i →
      ∀ u v : V, ¬ (C.labelGraph colour).Adj (i, u) (i, v)
  internal_labels_proper :
    ∀ (i : I) (colour : K) (hactive : colour ∉ palette i)
      (u v : V),
      (C.labelGraph colour).Adj (i, u) (i, v) →
        label i colour hactive u ≠ label i colour hactive v
  cross_edge_changes_membership :
    ∀ (i i' : I) (colour : K) (u v : V), i ≠ i' →
      (C.labelGraph colour).Adj (i, u) (i', v) →
        (colour ∈ palette i) ≠ (colour ∈ palette i')
  cross_edges_force_equal_active_labels :
    ∀ (i i' : I) (colour : K) (u u' v : V)
      (_hne : i ≠ i') (hactive : colour ∉ palette i),
      (C.labelGraph colour).Adj (i, u) (i', v) →
      (C.labelGraph colour).Adj (i, u') (i', v) →
        label i colour hactive u = label i colour hactive u'

end ErdosProblems.MulticolourTriangleRamsey
end
