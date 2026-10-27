public section

namespace CFSG.AGLEmbedding.TrialityTwo

open QuadraticMap Module CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin

open CFSG.ClassicalGroups.Orthogonal CFSG.AGLEmbedding.TrialityTwo.Seven

variable {K : Type} [Field K]

namespace Seven

theorem exists_solid :
    ∃ T : Submodule K (Fin 4 ⊕ Fin 4 → K), finrank K T = 4 ∧ ∀ x ∈ T, quadPlus 4 K x = 0 :=
  ⟨flag 4 K 4, finrank_flag le_rfl, fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩

end Seven
end CFSG.AGLEmbedding.TrialityTwo
end
