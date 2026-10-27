@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Branch-tree bound for a selector currently represented by `selector`. -/
def dispatchProgramTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (store : Store) (pcValue : ℕ) : Program → ℕ → ℕ
  | [], selector =>
      TM.resetBinaryWorkTime 1 selector.bits.length + 1 +
        executeInstructionTime tapes .halt pcValue store
  | instruction :: program, selector =>
      TM.branchWorkBlankTime
        (executeInstructionTime tapes instruction pcValue store)
        (TM.binaryPredTime (selector - 1) + 1 +
          dispatchProgramTime tapes store pcValue program (selector - 1))

end Machine
end RegisterStore
end RAM
end Complexity
end
