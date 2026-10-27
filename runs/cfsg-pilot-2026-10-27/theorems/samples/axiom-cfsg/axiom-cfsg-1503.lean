public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.ScalarReach

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.TableBExc.Three
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Chevalley.E7Three.ModelKernel
  CFSG.LieType.Chevalley.E7Three.Cube CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Chevalley.MaxTorusPart

section Weyl

theorem not_three_dvd_index_modelHomE7 :
    ¬ 3 ∣ modelHomE7.range.index := by
  rw [CFSG.StandardType.NoOffExc.index_eq_of_card card_range_modelHomE7
    CFSG.StandardType.NoOffExc.card_weyl_E7 (show 81 * 35840 = 2903040 by norm_num)
    (by norm_num)]
  norm_num

end Weyl
end CFSG.LieType.Chevalley.E7Three.ScalarReach
end
