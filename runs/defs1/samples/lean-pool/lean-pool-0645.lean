@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The slope and intercept of the inner D-wall line at angle `t`. -/
def capDAffine {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : ℝ) : ℝ × ℝ :=
  (Real.sin t / Real.cos t,
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.cos t)

end MovingSofa
end
end
end
end
end
end
end
end
