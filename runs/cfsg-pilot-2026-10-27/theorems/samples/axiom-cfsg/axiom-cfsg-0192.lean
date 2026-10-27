public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.LocalAnalysis.GLTheoremA.S10

open scoped commutatorElement

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem lemma102_cover_pSimple {p : ℕ} {I L : Subgroup G} {F : PQuot p I ≃* PQuot p L} :
    Nonempty (PSimple p I ≃* PSimple p L) := nonempty_pSimple_congr F

end S10
end CFSG.LocalAnalysis.GLTheoremA
end
