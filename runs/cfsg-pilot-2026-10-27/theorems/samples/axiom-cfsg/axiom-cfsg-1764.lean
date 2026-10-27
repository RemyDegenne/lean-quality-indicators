public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD

open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem F_le_S : d.F ≤ d.S := d.F_le_A₂.trans d.A₂_le_S

end Data.Hyp
end C7
end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
end
