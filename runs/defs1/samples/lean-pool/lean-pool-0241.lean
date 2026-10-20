@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

namespace UniversalBGGRootComplex

section

open scoped BigOperators

open MetricCodes.Spherical.HigherHarmonicYoung

/-- The positive root second used in the spherical-code argument. -/
def positiveRootSecond {r : ℕ} (α : PositiveRoot r) : Fin (r + 1) :=
  α.val.2

end
end UniversalBGGRootComplex
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
