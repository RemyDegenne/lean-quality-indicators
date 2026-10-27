public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

open CFSG.LocalAnalysis.GLTheoremA.S267.P3

variable {F : Type} [Field F] [Finite F] (ν : Type) [Fintype ν] [DecidableEq ν]

variable (hF : ∀ x : F, x ^ 3 = 1 → x = 1)

include hF

omit hF in
theorem J2sub_le_Jsub : J2sub ν (F := F) ≤ Jsub ν := by
  refine Subgroup.map_mono ?_
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin
end
