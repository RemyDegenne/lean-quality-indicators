public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open Subgroup

section Co3

open CFSG.Sporadic.Schreier.Co3 CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.RankThree.PartOne

theorem good427_co3 (x : Equiv.Perm (Fin 276)) (hx : x ∈ co3P) (hxo : orderOf x = 3) :
    Good427 (centralizer ({x} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := exists_conj_classes hx hxo
  rcases hc with rfl | rfl | rfl
  · obtain ⟨h3, -, -, hcard, hle, hnorm, hcent⟩ := caseA_spec
    exact Good427.conj hk h3 he (good427_of_selfCentralizing' hle hnorm
      (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent)
  · obtain ⟨h3, -, -, hcard, hle, hnorm, hcent⟩ := caseB_spec
    exact Good427.conj hk h3 he (good427_of_selfCentralizing' hle hnorm
      (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent)
  · obtain ⟨⟨hCeq, hcard⟩, -⟩ := caseC_spec
    refine Good427.conj hk yPerm_pow he (good427_of_not_five_dvd ?_)
    rw [← hCeq, hcard]
    norm_num

end Co3
end CFSG.RankThree.PartTwo.Sec4.Ronan148R
end
