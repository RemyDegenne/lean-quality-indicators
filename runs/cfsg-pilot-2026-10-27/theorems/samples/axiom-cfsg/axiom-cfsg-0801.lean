public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Assembly

theorem ggStepTwoAutKRestInput_of_last_exc (h3 : GGAutKCanonIIIInput)
    (h4 : GGAutKCanonIVInput) (hF : GGSixFieldFiveInput)
    (dF4 : GGLayerNotDFourTwoTag .F4) (dE6 : GGLayerNotDFourTwoTag .E6)
    (dE7 : GGLayerNotDFourTwoTag .E7) (dE8 : GGLayerNotDFourTwoTag .E8)
    (dTwE6 : GGLayerNotDFourTwoTag .twistedE6) (uF4 : GGLayerNotUFourAltSixTag .F4)
    (uE6 : GGLayerNotUFourAltSixTag .E6) (uE7 : GGLayerNotUFourAltSixTag .E7)
    (uE8 : GGLayerNotUFourAltSixTag .E8) (uTwE6 : GGLayerNotUFourAltSixTag .twistedE6)
    (h2 : GGStepTwoChoiceThreeTwoRest) : GGStepTwoAutKRestInput :=
  ggStepTwoAutKRestInput_of_last h3 h4 hF (ggLayerNotDFourTwoRound7_of_exc dF4 dE6 dE7 dE8 dTwE6)
    (ggLayerNotUFourAltSixRest_of_exc uF4 uE6 uE7 uE8 uTwE6) h2

end Assembly
end CFSG.StandardType
end
