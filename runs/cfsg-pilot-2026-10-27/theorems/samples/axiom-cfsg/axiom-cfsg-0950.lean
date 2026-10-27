public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.KFacts

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace HeringOF

theorem psuConj_eq_one_of_scalar {p f : ℕ} {F : Type} [Field F] {hF : UnitaryFieldData p f F}
    (A : unitaryIsom3 hF) {b : F}
    (hb : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = b • (1 : Matrix (Fin 3) (Fin 3) F)) :
    psuConj hF A = 1 := by
  have hcomm : ∀ g : GL (Fin 3) F, (A : GL (Fin 3) F) * g = g * (A : GL (Fin 3) F) := fun g =>
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, hb, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one])
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [psuConj_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [coe_suConj]
    calc (A : GL (Fin 3) F) * (g : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹ =
        (g : GL (Fin 3) F) * (A : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹ := by rw [hcomm]
      _ = (g : GL (Fin 3) F) := by group

end HeringOF
end CFSG.RankThree.PartTwo.Sec4
end
