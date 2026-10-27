public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Uni

variable {K : Type} [Field K] {m d : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 2)

include hm hK

theorem mem_fieldGU (hd : 3 ≤ d) (σ : K ≃+* K) :
    uFieldAut (unitaryData_two hm hK) (by omega) σ ∈
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m))) := by
  refine ⟨σ, fun x y hxy => ?_⟩
  have hxy' : ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ := hxy
  refine (uFieldAut_proj (unitaryData_two hm hK) (by omega) σ x).trans
    (congrArg (projH (StatedSU d (2 ^ m) K)) ?_)
  apply Subtype.ext
  apply Units.ext
  exact (coe_glAut σ (x : GL (Fin d) K)).trans hxy'.symm

end Uni
end CFSG.LocalAnalysis.GLTheoremA.Y10GField
end
