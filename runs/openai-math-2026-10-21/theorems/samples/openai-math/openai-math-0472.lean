namespace OAI

open Erdos970

noncomputable section

open scoped BigOperators

namespace Ostmann.Arithmetic.HistoryCRTIntegration

open Construction HistoryPairRepresentatives HistoryRepresentativeSourceSeparation

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem rootModulus_pos (h : History l) (hs : h.Supported V outside) : 0 < rootModulus h := by
  apply List.prod_pos
  intro n hn
  exact History.supported_root_positive hs n
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hn))

end Ostmann.Arithmetic.HistoryCRTIntegration
end
end OAI
