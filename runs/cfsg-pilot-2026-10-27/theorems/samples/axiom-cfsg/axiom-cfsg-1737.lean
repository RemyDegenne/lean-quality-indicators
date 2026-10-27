public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

section

open CFSG

open CFSG.RankThree.LocalRank

open CFSG.Open

open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)

open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem suzukiComponentStep_holds_conditional
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (P : Subgroup G) (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (e : G) (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    (hInput : SuzukiComponentStepInput (D := D) c P e) :
    SuzukiComponentStep hPSz hSzB hSzO hSzF c hON h7 P hNZ e hP3 hZ3 he he3 heZ := by
  intro J hJ hntriv
  rcases hInput J hJ hntriv with ⟨f, hf, hSz, z, hzN, hz3, hntriv', hWnorm, hCWN⟩ | h
  · have hJ3 : ¬ 3 ∣ Nat.card J :=
      not_three_dvd_card_of_nontrivial e c P hZ3 hJ hntriv
    exact suzuki_component_centralizer_of_action hJ hJ3 (componentsImage_isPGroup e) hWnorm
      hzN hz3 hSzB hSzO hSzF hSz hf hntriv' hCWN
  · exact h

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
end
