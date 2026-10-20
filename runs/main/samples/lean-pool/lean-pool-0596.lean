@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

theorem zeroJumpInstructionTM_isTransducer {n : ℕ}
    (tapes : ControlInstructionTapes n) (source target : ℕ) :
    (zeroJumpInstructionTM tapes source target).IsTransducer := by
  exact
    (entryLookupStaticTM_isTransducer tapes.data.lhsLookup source).seqTM
      (((setProgramCounterTM_isTransducer tapes.pc target).branchWorkBlankTM
        (TM.binarySuccTM_isTransducer tapes.pc)).seqTM
        (TM.resetBinaryWorkTM_isTransducer tapes.data.lhs))

end Machine
end RegisterStore
end RAM
end Complexity
end
