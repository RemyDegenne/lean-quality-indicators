public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Assembly.Dichotomy Equiv Equiv.Perm CFSG.Sporadic.Th.Max3

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)

include d

theorem self_mul_self : (u : J ⧸ Subgroup.center J) * (u : J ⧸ Subgroup.center J) = 1 := by
  rw [← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x),
    d.caseC3BCD.caseC3Word_mul_self_eq_one_iff]
  decide

end E1Data
end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
end
