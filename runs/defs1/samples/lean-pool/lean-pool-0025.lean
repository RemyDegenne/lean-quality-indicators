@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Recursive work-independent streaming-loop bound. -/
def initialInputLoopTime {n : ℕ} (tapes : ControlInstructionTapes n) :
    ℕ → ℕ → List Bool → ℕ
  | _, _, [] => 1
  | address, count, bit :: rest =>
      let bodyTime := if bit then
        rewindEntryEncodeRestoreTime (address, 1) + 1 +
          TM.binarySuccTime count + 1 + TM.binarySuccTime address
        else TM.binarySuccTime address
      1 + bodyTime + 1 +
        initialInputLoopTime tapes (address + 1)
          (count + if bit then 1 else 0) rest

end Machine
end RegisterStore
end RAM
end Complexity
end
