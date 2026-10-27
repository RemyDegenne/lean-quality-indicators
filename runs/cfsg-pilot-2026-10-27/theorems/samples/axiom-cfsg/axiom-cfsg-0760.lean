public noncomputable section

namespace CFSG.RankThree.Native

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier

open scoped commutatorElement

theorem card_mcl275FiveQ : Nat.card mcl275FiveQ = 125 :=
  linesOK_card mcl275FiveKeys_lt mcl275Five_lines_ok

end CFSG.RankThree.Native
end
