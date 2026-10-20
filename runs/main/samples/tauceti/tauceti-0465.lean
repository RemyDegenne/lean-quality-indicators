public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

namespace GraphCell

theorem boundary_def (K : GraphCell) (d : Coordinate) :
    K.boundary d = BoundaryChain.cellBoundary d K.a K.b K.lowerFun K.upperFun
      K.continuous_lowerFun.continuousOn K.continuous_upperFun.continuousOn := (rfl)

end GraphCell
end TauCeti.Green
end
end
