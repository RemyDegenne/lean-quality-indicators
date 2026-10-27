public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ComponentClassification.RankTwoStandard

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS RuSModel

namespace RuSModel

theorem eta_mem : ((1, 6, 2) : Lin8) ∈ glList := by decide +kernel

end RuSModel
end CFSG.ComponentClassification.GMS78
end
