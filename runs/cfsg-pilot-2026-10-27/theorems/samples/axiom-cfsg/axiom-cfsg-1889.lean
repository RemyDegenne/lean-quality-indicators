public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGNbrLangAxisInnerOn.or {S S' : ℕ → LargeEvenLabel → Prop} (h : GGNbrLangAxisInnerOn S)
    (h' : GGNbrLangAxisInnerOn S') : GGNbrLangAxisInnerOn fun p lab => S p lab ∨ S' p lab := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  refine NbrLangTypeA.ggMarkingAll_of_and (h G p B Bs x L D J hC y K hK hN)
    (h' G p B Bs x L D J hC y K hK hN) ?_
  rintro lab R _ I F θ hQ hQ' (hS | hS)
  · exact hQ hS
  · exact hQ' hS

end CFSG.StandardType
end
