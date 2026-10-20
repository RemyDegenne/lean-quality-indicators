public section

universe u v w

namespace TauCeti

open FirstOrder

open scoped Ordinal

variable {L : Language.{u, v}} [L.IsRelational]

variable {M : Type w} [L.Structure M] {n : ℕ}

variable (M)

variable {M}

theorem internalScottRank_le_succ_selfStabilizationOrdinal :
    internalScottRank (L := L) M ≤ selfStabilizationOrdinal (L := L) M + 1 := by
  rw [internalScottRank_def]
  exact Ordinal.iSup_le fun p => add_le_add (orbitRank_le_selfStabilizationOrdinal p.2) le_rfl

end TauCeti
end
