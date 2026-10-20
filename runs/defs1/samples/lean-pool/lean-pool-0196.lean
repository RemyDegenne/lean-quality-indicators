@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHierarchy

section

open MeasureTheory

open scoped BigOperators Interval

/-- The stieltjes phase product used in the spherical-code argument. -/
def stieltjesPhaseProduct {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) : ℝ :=
  t * (∏ i : Fin r, (t + ((b i) * (1 + (b i))))) /
    (∏ i : Fin (r + 1), (t + ((a i) * (1 + (a i)))))

end
end HigherHierarchy
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
