public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Recognition.PresentedWords CFSG.CosetTable

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

section DP

theorem tabRep_letInv (j : Fin 6) : TabRep (letInv ())[j.val]! (dP j)⁻¹ :=
  invsOK_spec cert_inv (by rw [letArr_size_eq]; exact j.isLt) (tabRep_dP j)

end DP
end CFSG.Sporadic.Th.Recog
end
