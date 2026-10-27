public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

theorem hn_cover_A :
    ∀ z : JH, conjR (jR aJ) z = z → orderOf z = 5 →
      ∃ l : List JH, (∀ g ∈ l, g * z = z * g) ∧
        5 ∣ orderOf ((l.map fun g => MulAut.conj g * conjR (jR aJ) * (MulAut.conj g)⁻¹).prod) :=
  hn_cover_of_ok hn_class_a_check hn_card_CJ.1 (k := 3) (m := 1419264) (by norm_num)
    (by norm_num) rfl

end CFSG.RankThree.PartOne.SPOR
end
