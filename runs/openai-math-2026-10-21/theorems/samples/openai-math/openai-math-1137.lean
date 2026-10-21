namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringGlobalConfiguration

open Turing PoweringMachineGlobal

theorem headerDarts_ne_scratch (n : Nat) :
    headerDarts n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerDarts_ne_placement n _

end MinUncutGames.Foundations.Complexity.PoweringGlobalConfiguration
end OAI
