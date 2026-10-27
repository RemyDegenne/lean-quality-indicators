public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem sqdvd_two_Fi22 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (h : p ^ 2 ∣ 64561751654400) :
    SporadicTwoPair .Fi22 p :=
  sqdvd_two_of (by norm_num) {2, 3, 5, 7, 11, 13} (by norm_num [Nat.primeFactors]) (by decide) hp hp5 h

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
end
