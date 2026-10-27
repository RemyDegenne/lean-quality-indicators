public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

open Matrix

open CFSG.LocalAnalysis.ComponentInitial

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

noncomputable section

theorem s16c11_case2lie_sp_unipotent_le_flagStabilizer {r : ℕ} {K : Type} [Field K] :
    SymplecticFlag.unipotent r K ≤ SymplecticHigher.flagStabilizer r K (Set.Icc 2 r) :=
  SymplecticFlag.unipotent_le_borelSubgroup.trans
    (SymplecticHigher.borelSubgroup_le_flagStabilizer fun _ hi => (Set.mem_Icc.mp hi).2)

end
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
