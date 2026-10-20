namespace P2MW.S_Ihara_amalgamToGamma0Away_injective

namespace Ihara

namespace SolA2

p2m_open

open Matrix CongruenceSubgroup

open scoped MatrixGroups

section PingPongDatum

variable (N q : ℕ)

variable {N q}

theorem amalgamToGamma0Away_injective (hq : q.Prime) (hqN : N.Coprime q) :
    Function.Injective (amalgamToGamma0Away N q) :=
  (amalgamToGamma0Away_injective_iff N q).mpr (amalgamToAway_injective hq hqN)

end PingPongDatum
end SolA2
end Ihara
end P2MW.S_Ihara_amalgamToGamma0Away_injective
