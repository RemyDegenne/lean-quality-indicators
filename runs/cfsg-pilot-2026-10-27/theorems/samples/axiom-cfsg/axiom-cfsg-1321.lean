public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open NbrInnerMore

section Main

theorem ggNbrInnerWeylOn_nsE6 : GGNbrInnerWeylOn GGNbrNsE6Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc => NbrInnerMore.not_markedModel_char_ne_two_E6 h.1 hX hc)
    (fun _ _ hp _ _ h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_E6 hp h.1 h.2.1)
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_E6 hlab h hX hlab' hc' hX' c)

end Main
end CFSG.StandardType
end
