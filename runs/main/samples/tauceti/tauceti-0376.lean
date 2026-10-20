public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval TauCeti.Probability.AldousHoover

namespace TauCeti

namespace DenseGraphLimits

variable (g : I × I × I → Bool)

@[simp]
theorem codingGraphon_apply (hg : Measurable g) (x y : I) :
    codingGraphon g hg x y = volume.real {t : I | g (x, y, t) = true ∨ g (y, x, t) = true} :=
  (rfl)

end DenseGraphLimits
end TauCeti
end
end
