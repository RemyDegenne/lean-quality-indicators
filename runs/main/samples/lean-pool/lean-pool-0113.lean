@[expose] public section

namespace MatchingLogic

open Set

noncomputable section

variable {S : Signature}

theorem witnessCollapseTheory_not_freshWitnessed :
    ¬ FreshWitnessed witnessCollapseTheory := by
  intro hFresh
  let e : Pattern WitnessCollapseSig Nat := .ex 0 (.var 0)
  have he : e ∈ witnessCollapseTheory := by
    change true ∈ witnessCollapseModel.denote witnessCollapseRho e
    simp [e]
  obtain ⟨y, hyFresh, hyImp⟩ := hFresh he
  have hyNe : y ≠ 0 := by
    simpa [Pattern.allVars] using hyFresh
  change true ∈ witnessCollapseModel.denote witnessCollapseRho
    (.imp e (Pattern.captureAvoidingSubst 0 y (.var 0))) at hyImp
  have hePoint : true ∈ witnessCollapseModel.denote witnessCollapseRho e := he
  have hinstance :
      true ∉ witnessCollapseModel.denote witnessCollapseRho
        (Pattern.captureAvoidingSubst 0 y (.var 0)) := by
    rw [witnessCollapseModel.denote_captureAvoidingSubst]
    simp [witnessCollapseRho, hyNe]
  simp only [denote_imp, Set.mem_union, Set.mem_compl_iff] at hyImp
  exact hyImp.elim (fun hnot => hnot hePoint) (fun hmem => hinstance hmem)

end
end MatchingLogic
end
