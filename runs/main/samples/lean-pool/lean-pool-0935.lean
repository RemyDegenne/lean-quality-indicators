@[expose] public section

namespace LowGenus.GenusFourRow096Pencil

open Utilities

open Utilities.Certificate

open Utilities.Certificate.SubdivisionGraph

open Utilities.Certificate.SubdivisionRamp

open AtanasovRanganathan.GenusFourCubicAtlas

section ChipBookkeeping

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p}

theorem pathVertex_eq_head (e : Fin p) (q : spec.PathPosition e)
    (h : q.val = spec.length e) :
    spec.pathVertex e q = spec.coreVertex (spec.core.head e) := by
  have hpos := spec.length_pos e
  unfold SubdivisionGraph.Spec.pathVertex
  rw [dite_eq_right (by omega), dite_eq_left h]

end ChipBookkeeping
end LowGenus.GenusFourRow096Pencil
end
