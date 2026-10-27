public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang

section D4

variable {K : Type} [Field K]

theorem d4P_inv_mul_rootDiagUnit_mul (b : Fin Tag.D4.rank → Kˣ) :
    (d4P K)⁻¹ * rootDiagUnit Tag.D4 b * d4P K = rootDiagUnit Tag.D4 fun i => b (d4Rho i) := by
  have h := diagramMap_mul_rootDiagUnit (K := K) (t := TwistTag.D4) (fun i => b (d4Rho i))
  have e : (fun i => (fun i => b (d4Rho i)) (TwistTag.D4.perm.symm i)) = b :=
    funext fun i => congrArg b (Equiv.apply_symm_apply d4Rho i)
  rw [e] at h
  calc (d4P K)⁻¹ * rootDiagUnit Tag.D4 b * d4P K =
      (d4P K)⁻¹ * (rootDiagUnit Tag.D4 b * d4P K) := by rw [mul_assoc]
    _ = (d4P K)⁻¹ * (d4P K * rootDiagUnit Tag.D4 fun i => b (d4Rho i)) := by
        rw [show rootDiagUnit Tag.D4 b * d4P K =
          d4P K * rootDiagUnit Tag.D4 (fun i => b (d4Rho i)) from h.symm]
    _ = rootDiagUnit Tag.D4 fun i => b (d4Rho i) := by group

end D4
end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd
end
