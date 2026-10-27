public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedOmega StatedQuadPlus)

open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem fixedLowerBoundAt_POmegaPlus : FixedLowerBoundAt .POmegaPlus := by
  intro K _ _ n ℓ f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf α hαp hαin
  have hcl : StatedClassicalModel K .POmegaPlus n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hp2 : p ≠ 2 := by omega
  have hD4 : ¬ (n = 4 ∧ p = 3) := fun h => by omega
  have hpos : 0 < p := hp.pos
  obtain ⟨f₁, hf₁, hdvd⟩ := card_fixed_POmegaPlus hcl hp hp2 hD4 α hαp hαin
  have : f₁ = f₀ := by
    have := hf.symm.trans hf₁
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  subst this
  exact hdvd

end KFAE
end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
end
