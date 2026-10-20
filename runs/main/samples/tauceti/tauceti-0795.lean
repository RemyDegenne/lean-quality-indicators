public section

namespace TauCeti

namespace GridState

variable {n : ℕ}

theorem insertPoint_castSucc_swapColumns (x : GridState n) (s : Fin n) (newRow : Fin (n + 1)) :
    (x.insertPoint s.castSucc newRow).swapColumns s.castSucc s.succ =
      x.insertPoint s.succ newRow := by
  simpa only [splitPoint, Fin.succAbove_castSucc_self] using
    x.splitPoint_castSucc_eq_insertPoint s newRow

end GridState
end TauCeti
end
