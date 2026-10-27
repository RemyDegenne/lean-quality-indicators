public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.Assembly CFSG.StandardType

section Main

theorem line63StepOneQ2_holds :
    Line63StepOneQ2 := by
  intro G _ _ B Bs x L D J hcfg hlt K _ _ hK hL θ hBN hBI z hzL hzc hz3
  by_contra hz1
  exact stepOne_two hcfg hlt hK hL θ hBN hBI hzL hzc hz3 hz1

end Main
end CFSG.StandardType.Line63.H5
end
