public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartOne
  CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.HardMathSupport.Lang.Proving
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux

open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem upD42Chev2Out_d4_holds : UpD42Chev2Out
    (fun d => match d with | .D r _ => r = 4 | _ => False) := by
  intro S _ _ _ _ ⟨d, hv⟩ hd hc ⟨e⟩ α hout hx
  cases d with
  | D r q =>
    obtain rfl : r = 4 := hd
    have hp : q.p = 2 := hc
    have hC : StatedClassicalModel S .POmegaPlus 4 2 q.exponent := by
      rw [← hp]
      exact (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp
        (blueprintLieModel_D 4 q hv e)
    have hC0 := hC
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hC0
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hC.1.2.1 hK
    let E := coordinatePlusWitnessEquiv K eK
    by_cases hE : MulAut.congr E α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)
    · have hf := (rank_field_of_upD42Pumpup_omega_plus_semilinear hC K hK eK
        α hout hE hx).2
      exact Or.inr (Or.inr ⟨⟨.D 4 q, hv⟩, ⟨rfl, hp, hf⟩, ⟨e⟩⟩)
    · exact (not_upD42Pumpup_d4_off_semilinear hE (hx.congr E)).elim
  | _ => exact hd.elim

end CFSG.HardMathSupport.Dickson.Sec6
end
