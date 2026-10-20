section

section

@[expose] public section

noncomputable section

namespace NavierStokes.FlatCovariance

open Matrix Set

open SmoothCovariance (Mat2 Vec2)

open FlatCutoff (edge)

open scoped ContDiff Topology

theorem determinant_columns (G : Mat2) (c : Vec2) :
    (columns G c).det = c 0 * c 1 * G.det := by
  simp only [Matrix.det_fin_two, columns]
  ring

end NavierStokes.FlatCovariance
end
end
end
end
