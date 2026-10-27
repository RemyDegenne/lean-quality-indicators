public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu

open scoped commutatorElement

theorem co2FiveA_normal : (co2FiveA.subgroupOf co2FiveC0).Normal :=
  co2Five_structures.a_normal

end CFSG.RankThree.Native
end
