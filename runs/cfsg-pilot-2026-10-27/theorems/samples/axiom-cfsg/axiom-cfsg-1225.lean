public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem i1415SevenSporS_of_residual
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hres : AltRow 7 .B ∧ AltRow 7 .M ∧ AltRow 7 .He) : I1415SevenSporS := by
  refine (sporAltNoComp_iff 7).2 fun s => ?_
  by_cases hsB : s = .B
  · exact hsB ▸ hres.1
  by_cases hsM : s = .M
  · exact hsM ▸ hres.2.1
  by_cases hsHe : s = .He
  · exact hsHe ▸ hres.2.2
  by_cases hsHN : s = .HN
  · exact hsHN ▸ (altRow_HN_Co1 hOut hbr (Or.inl rfl)).1
  by_cases hsCo : s = .Co1
  · exact hsCo ▸ (altRow_HN_Co1 hOut hbr (Or.inl rfl)).2
  exact altRow_of_srow (by norm_num) (srow_three hOut hbr hOrd hb hsB hsM hsHe hsHN hsCo)

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows
end
