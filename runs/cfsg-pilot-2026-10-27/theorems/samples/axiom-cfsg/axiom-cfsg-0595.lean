public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short

theorem th_wordLin_conj
    {c w : List Native.Gen} (h : thConjCheck c w = true) :
    wordLin c * wordLin thRhoT = wordLin w * wordLin c := by
  have := wordLin_eq_of_thIdCheck h
  rwa [wordLin_append, wordLin_append] at this

end CFSG.Monster.Existence
end
