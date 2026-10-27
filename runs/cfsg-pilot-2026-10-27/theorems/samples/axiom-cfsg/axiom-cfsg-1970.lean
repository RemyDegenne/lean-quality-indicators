public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  {S : Subgroup (Fin r → Kˣ)}

theorem eichler_mem_Rts_of_Wsub {c₀ : Fin r ⊕ Fin r} (hc₀ : TrivOn S c₀) {w : (Fin r ⊕ Fin r → K) × A}
    (hw : w ∈ Wsub (K := K) (A := A) S) (hpol : polar (quadTail r qA) (hypVec K A c₀) w = 0) :
    eichler (quadTail r qA) (hypVec K A c₀) w ∈ Rts qA S := by
  have hw1 : w.1 c₀.swap = 0 := by
    rw [polar_comm, polar_hypVec] at hpol
    exact hpol
  have hmem : w ∈ RcSub qA S c₀ := by
    rw [vec_expand w]
    refine add_mem (AddSubgroup.sum_mem _ fun j _ => ?_) (tail_mem_RcSub hc₀ w.2)
    by_cases hj : TrivOn S j
    · by_cases hcj : coordIdx j = coordIdx c₀
      · rcases coordIdx_eq_cases hcj with rfl | rfl
        · exact smul_self_mem_RcSub _
        · rw [hw1, zero_smul]
          exact zero_mem _
      · exact smul_hypVec_mem_RcSub hc₀ hj hcj _
    · rw [hw j hj, zero_smul]
      exact zero_mem _
  exact hmem.2

end CFSG.RankThree.PartOne.K159H
end
