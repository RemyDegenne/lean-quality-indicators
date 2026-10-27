public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type*} [Group G]

theorem glaDelta_le_glaPPrimeCoreOf {p : ℕ} {D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    GLADelta p D ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) :=
  iInf_le_of_le d (iInf_le_of_le hd (iInf_le _ hd1))

end CFSG.HardMathSupport.Solomon.Coordinator
end
