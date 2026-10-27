public section

namespace CFSG.Quasithin.RuType.J47

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Quasithin.RuRank3
  CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native

open scoped Pointwise

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

theorem eP_mem_H :
    eP ∈ twoF4H :=
  (mem_twoF4H_iff eP_mem_A).2 eP_zero

end CFSG.Quasithin.RuType.J47
end
