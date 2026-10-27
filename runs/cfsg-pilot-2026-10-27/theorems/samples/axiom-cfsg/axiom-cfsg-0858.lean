public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.CGT6
  CFSG.CGT.PushingUpLit.CGT6X.End3 CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.Open (StatedClassicalModel)

theorem end411_of'
    (hL34 : End411L34') : End411' := by
  intro V _ _ hV G T Y cfg f hf hY hT hmod
  rcases hmod with hPSL | hPSU
  · by_cases h2 : f = 2
    · subst h2
      exact hL34 V hV G T Y cfg hY hT hPSL
    · exact end411_of_linear' hV cfg hY hT (by omega) hPSL
  · exact end411_of_unitary' hV cfg hY hT hf hPSU

end CFSG.CGT.PushingUpLit.CGT6K1
end
