namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology

open Set Function Filter MeasureTheory

theorem AffineLineCurve.isProperMap {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) : IsProperMap u :=
  isProperMap_iff_tendsto_cocompact.mpr ⟨hu.1.continuous,hu.tendsto_cocompact⟩

end HigherDimensionalBallPacking.Rigidity
end
end OAI
