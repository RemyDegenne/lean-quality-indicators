public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.AGLEmbedding.LieOut CFSG.AGLEmbeddingD2.ParabLevi

section Rad

variable {m : ℕ} {F : Type} [Field F]

theorem toStd_rootVec {a b : Fin (m + 1)} (hab : a.val < b.val) :
    toStd m (rootVec a b) = Pi.single a 1 - Pi.single b 1 := by
  funext p
  simp only [toStd, rootVec, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> first | omega | simp_all <;> omega

end Rad
end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
end
