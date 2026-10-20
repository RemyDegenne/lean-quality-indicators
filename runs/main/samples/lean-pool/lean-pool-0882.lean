@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators

namespace DeterminantVectors

theorem pderiv_even_isotropicVariable {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (a p i j : Fin (r + 1)) :
    MvPolynomial.pderiv (variableIndex a (evenCoordinate h p))
        (isotropicVariable h i j) =
      if a = i ∧ p = j then 1 else 0 := by
  classical
  simp [isotropicVariable, Pi.single_apply, variableIndex_eq_iff, evenCoordinate_inj,
    evenCoordinate_ne_oddCoordinate, eq_comm]

end DeterminantVectors
end
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
