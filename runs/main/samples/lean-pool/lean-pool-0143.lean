@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators

namespace DeterminantVectors

@[simp] theorem oddCoordinate_inj {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (i j : Fin (r + 1)) :
    oddCoordinate h i = oddCoordinate h j ↔ i = j := by
  constructor
  · intro heq
    apply Fin.ext
    have hv := congrArg Fin.val heq
    simp only [oddCoordinate_val] at hv
    omega
  · rintro rfl
    rfl

end DeterminantVectors
end
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
