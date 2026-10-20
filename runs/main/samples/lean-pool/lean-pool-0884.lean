@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

namespace UniversalBGGRootComplex

section

open scoped BigOperators

open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootJointHarmonicActionUpperRootStructureCross_polynomial_apply
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam k)
    (S : AdmissibleRootWedge lam k) :
    (((rootJointHarmonicActionUpperRootStructureCross n lam k f S).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam S)) :
      PolynomialSpace r n) =
      ∑ α : PositiveRoot r,
        if hα : α ∈ S.val.val then
          ∑ β : PositiveRoot r,
            if hβ : β ∈ S.val.val then 0
            else if hadm : ∀ i,
                0 ≤ signedRootWeight lam (insert β (S.val.val.erase α)) i then
              ∑ γ : PositiveRoot r,
                if _hγ : rootStructureConstant β γ α = 0 then 0
                else (rootSwapExteriorHodgeSign S α β *
                    rootStructureConstant β γ α) •
                  polarization r n (positiveRootFirst γ) (positiveRootSecond γ)
                    ((f (rootAdmissibleSwap lam S α β hα hβ hadm)).val :
                      PolynomialSpace r n)
            else 0
        else 0 := by
  classical
  rw [rootJointHarmonicActionUpperRootStructureCross_apply]
  simp only [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs with hα
  · simp only [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro β _
    split_ifs with hβ hadm
    · simp only [ZeroMemClass.coe_zero]
    · simp only [Submodule.coe_sum]
      apply Finset.sum_congr rfl
      intro γ _
      split_ifs with hγ
      · simp only [ZeroMemClass.coe_zero]
      · simp only [Submodule.coe_smul]
        rw [rootSwapUpperStructureEdge_coe]
    · simp only [ZeroMemClass.coe_zero]
  · simp only [ZeroMemClass.coe_zero]

end
end UniversalBGGRootComplex
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
