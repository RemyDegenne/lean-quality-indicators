@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace GerverSofa.PartF.Phases

theorem phase1 (d : Reduced.Params) (t : ℝ) :
    Romik.rot t (closed1 d t) = Romik.path1 (dictionary d) t := by
  apply Prod.ext
  · dsimp [Romik.rot, closed1, Romik.path1, Romik.addK, dictionary, ell]
    linear_combination (1 - 3 / 2 * (1 - V1 d)) * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, closed1, Romik.path1, Romik.addK, dictionary, ell]
    linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq t

end GerverSofa.PartF.Phases
end
end
end
end
end
end
end
end
