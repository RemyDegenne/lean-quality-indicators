@[expose] public section

open NRR NRR.Geometry MeasureTheory

namespace NRR.PowerDiagram

variable {n : ℕ}

theorem bodyCellSet_isCompact (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (i : Fin n) :
    IsCompact (bodyCellSet K s w i) :=
  K.isCompact.inter_right (cell_isClosed s w i)

end NRR.PowerDiagram
end
