@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

namespace UniversalBGGRootComplex

section

open scoped BigOperators

open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootPolynomialIncludedActionHodgeDiagonal_eq_subtype_sums
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (∑ α : PositiveRoot r,
      if α ∈ S.val.val then
        if 0 < rootWedgeWeight lam S (positiveRootFirst α) then
          polarization r n (positiveRootFirst α) (positiveRootSecond α)
            (polarization r n (positiveRootSecond α) (positiveRootFirst α)
              (p.val : PolynomialSpace r n))
        else 0
      else 0) =
      (∑ α : IncludedDescendingPositiveRoot lam S,
        polarization r n (positiveRootFirst α.val)
          (positiveRootSecond α.val)
          (polarization r n (positiveRootSecond α.val)
            (positiveRootFirst α.val) (p.val : PolynomialSpace r n))) +
      (∑ α : IncludedNondescendingPositiveRoot lam S,
        polarization r n (positiveRootFirst α.val)
          (positiveRootSecond α.val)
          (polarization r n (positiveRootSecond α.val)
            (positiveRootFirst α.val) (p.val : PolynomialSpace r n))) := by
  classical
  let F : PositiveRoot r → PolynomialSpace r n := fun α =>
    polarization r n (positiveRootFirst α) (positiveRootSecond α)
      (polarization r n (positiveRootSecond α) (positiveRootFirst α)
        (p.val : PolynomialSpace r n))
  let P : PositiveRoot r → Prop := fun α =>
    α ∈ S.val.val ∧
      rootWedgeWeight lam S (positiveRootSecond α) <
        rootWedgeWeight lam S (positiveRootFirst α)
  let Q : PositiveRoot r → Prop := fun α =>
    α ∈ S.val.val ∧
      0 < rootWedgeWeight lam S (positiveRootFirst α) ∧
        rootWedgeWeight lam S (positiveRootFirst α) ≤
          rootWedgeWeight lam S (positiveRootSecond α)
  change
    (∑ α : PositiveRoot r,
      if α ∈ S.val.val then
        if 0 < rootWedgeWeight lam S (positiveRootFirst α) then F α
        else 0
      else 0) =
      (∑ α : {α : PositiveRoot r // P α}, F α.val) +
        (∑ α : {α : PositiveRoot r // Q α}, F α.val)
  rw [sum_rootSubtype_eq_indicator P F,
    sum_rootSubtype_eq_indicator Q F, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hmem : α ∈ S.val.val
  · by_cases hpos : 0 < rootWedgeWeight lam S (positiveRootFirst α)
    · by_cases hdesc :
        rootWedgeWeight lam S (positiveRootSecond α) <
          rootWedgeWeight lam S (positiveRootFirst α)
      · have hnon : ¬ rootWedgeWeight lam S (positiveRootFirst α) ≤
            rootWedgeWeight lam S (positiveRootSecond α) := by omega
        simp only [hmem, ↓reduceIte, hpos, hdesc, and_self, hnon, and_false, add_zero, P, Q]
      · have hnon : rootWedgeWeight lam S (positiveRootFirst α) ≤
            rootWedgeWeight lam S (positiveRootSecond α) := by omega
        simp only [hmem, ↓reduceIte, hpos, hdesc, and_false, hnon, and_self, zero_add, P, Q]
    · have hdesc : ¬ rootWedgeWeight lam S (positiveRootSecond α) <
          rootWedgeWeight lam S (positiveRootFirst α) := by omega
      simp only [hmem, ↓reduceIte, hpos, hdesc, and_false, false_and, add_zero, P, Q]
  · simp only [hmem, ↓reduceIte, false_and, add_zero, P, Q]

end
end UniversalBGGRootComplex
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
