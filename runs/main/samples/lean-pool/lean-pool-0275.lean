@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace MovingSofa

theorem inner_tangentVector_zero (p : Point) :
    inner ℝ p (tangentVector ((0 : ℝ) : Real.Angle)) = p 1 := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

end MovingSofa
end
end
end
end
end
end
end
end
