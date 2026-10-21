namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg998 : RowSquare [6,1,1,1,1] [2,2,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [8,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB998 sgT998 sgFlag998
  change solveCompact 10 (.full [8,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB998 sgT998) sgFlag998 ≠ 0
  rw [sgCert998]
  norm_num

end UniversalTensorSquare
end
end
end OAI
