section

section

@[expose] public section

noncomputable section

namespace EulerTopBlockTimeNorm

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution

open scoped Topology

variable {X Y Z I : Type*} [Fintype I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem mapped_pathLp_sub (T : ℝ) (hT : 0 ≤ T) (A : X →L[ℝ] Y)
    (u v : C(Icc (0 : ℝ) T, X)) :
    pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) (u-v)) =
      pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) u) -
      pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) v) :=
  (congrArg (pathLp T hT) (map_sub (A.compLeftContinuous ℝ (Icc (0 : ℝ) T)) u v)).trans
    (pathLp_sub T hT _ _)

end EulerTopBlockTimeNorm
end
end
end
end
