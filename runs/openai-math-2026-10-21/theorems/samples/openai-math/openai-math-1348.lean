namespace OAI

namespace PartitionConsistency.ProbeAlgebra.Word

universe u v

open DiagramOrder Classical

variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (H : HeightCost (LeftDivOrder M))

theorem gateCap_pos (w : Word A b) : 0 < gateCap A b H w := by
  classical
  unfold gateCap
  split_ifs
  · exact H.cost_pos _
  · exact zero_lt_one

end PartitionConsistency.ProbeAlgebra.Word
end OAI
