@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace NavierStokes.SignedCovariance

open Set Function Filter MeasureTheory Matrix

open PartitionedCovariance

open scoped BigOperators Topology ContDiff

/-- Tangent with, constructed using `wave`. -/
noncomputable def tangentWith {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (a : Vec2) (q : ℝ) (x : SlotColoring.Position) (j i : Fin 2) : Plane → ℝ → ℝ :=
  wave (outer * (Real.sqrt ε * a j * mask D U q x))
    (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j i) (P.modes j) (P.phases j)

end NavierStokes.SignedCovariance
end
end
