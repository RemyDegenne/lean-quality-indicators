@[expose] public section

namespace LowGenus.GenusFourRow096Pencil

open Utilities

open Utilities.Certificate

open Utilities.Certificate.SubdivisionGraph

open Utilities.Certificate.SubdivisionRamp

open AtanasovRanganathan.GenusFourCubicAtlas

section Regime1March

open Utilities.Certificate.SubdivisionRamp

variable {spec : SubdivisionGraph.Spec 6 9}

theorem one_le_tauDiv_of_eq (spec : SubdivisionGraph.Spec 6 9)
    (j : spec.PathPosition 0) (k : spec.PathPosition 3) (m : spec.PathPosition 8)
    (u : Fin 6)
    (h : spec.pathVertex 0 j = spec.coreVertex u ∨
      spec.pathVertex 3 k = spec.coreVertex u ∨
      spec.pathVertex 8 m = spec.coreVertex u) :
    1 ≤ tauDiv spec j k m (spec.coreVertex u) := by
  have hnn : ∀ w : spec.graph.V,
      0 ≤ oneChip (G := spec.graph) w (spec.coreVertex u) := by
    intro w
    simp only [oneChip]
    split_ifs <;> norm_num
  have hone : ∀ w : spec.graph.V, w = spec.coreVertex u →
      oneChip (G := spec.graph) w (spec.coreVertex u) = 1 := by
    intro w hw
    simp [oneChip, hw]
  simp only [tauDiv, Pi.add_apply]
  rcases h with h | h | h
  · have h1 := hone _ h
    have h2 := hnn (spec.pathVertex 3 k)
    have h3 := hnn (spec.pathVertex 8 m)
    omega
  · have h1 := hone _ h
    have h2 := hnn (spec.pathVertex 0 j)
    have h3 := hnn (spec.pathVertex 8 m)
    omega
  · have h1 := hone _ h
    have h2 := hnn (spec.pathVertex 0 j)
    have h3 := hnn (spec.pathVertex 3 k)
    omega

end Regime1March
end LowGenus.GenusFourRow096Pencil
end
