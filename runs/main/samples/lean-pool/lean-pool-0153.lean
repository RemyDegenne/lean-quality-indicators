@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section4

theorem classicalWordSplits_leftLength_count (w : List (Fin 2)) (q : ℕ) :
    ((classicalWordSplits w).filter (fun p => p.1.length = q)).length =
      w.length.choose q := by
  exact Classical.classicalWordSplits_leftLength_count
    w q

end AVenhance.Infra.Section4
end
end
