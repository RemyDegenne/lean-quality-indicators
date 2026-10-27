public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

open Stroth42Core

namespace Type310

attribute [local simp] Type310.ρM Type310.uvA Type310.tM Type310.uvM Type300.ρM Type300.uvA
  Type300.tM Type300.uvM psiM ofCols_apply Matrix.mul_apply Fin.sum_univ_three Matrix.mulVec
  dotProduct Matrix.one_apply t300_k Nat.add_sub_cancel

theorem killFact (m : ℕ) (hm : 2 ≤ m) : KillFact (StrothTypeIndex.t310 m hm) :=
  KillFact.of_equiv (psi m hm) Type300.killFact (psi_φuv hm) (psi_φt hm) (psi_φρ hm) (psi_zero hm)

end Type310
end CFSG.CGT.Stroth77
end
