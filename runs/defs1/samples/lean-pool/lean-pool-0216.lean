@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Complete fixed-program halt-test bound. -/
def programHaltTime {n : ℕ} (tapes : ControlInstructionTapes n)
    (program : Program) (pcValue : ℕ) : ℕ :=
  TM.binaryCopyTime pcValue 0 + 1 +
    dispatchHaltTime tapes program pcValue

end Machine
end RegisterStore
end RAM
end Complexity
end
