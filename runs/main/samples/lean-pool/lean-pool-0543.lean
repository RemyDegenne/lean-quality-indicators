@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

namespace MixedSignature

section

open scoped BigOperators InnerProductSpace TensorProduct

open MetricCodes.Spherical.HigherChannel

theorem raiseWeight_injective_fixed_row {r : ℕ}
    (row : Fin (r + 1)) :
    Function.Injective (fun lam : Fin (r + 1) → ℕ =>
      raiseWeight lam row) := by
  intro lam mu heq
  funext i
  have hi := congrFun heq i
  by_cases h : i = row
  · subst i
    simpa only using Nat.add_right_cancel (show lam row + 1 = mu row + 1 by simpa [raiseWeight]
      using hi)
  · simpa only [raiseWeight, ne_eq, h, not_false_eq_true, Function.update_of_ne] using hi

end
end MixedSignature
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
