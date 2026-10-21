namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.PortTables

variable {n d : Nat}

theorem inputBits_injective (ports : Nat) : Function.Injective (@inputBits ports) :=
  (encoding ports).encode_injective

end UniqueGamesTheorem.Foundations.PCP.PortTables
end
end OAI
