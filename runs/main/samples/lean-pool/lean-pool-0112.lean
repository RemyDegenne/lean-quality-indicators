@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

namespace EntryMatchTapes

@[simp] theorem cleanupIdx_six {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.cleanupIdx 6 = tapes.result := rfl

end EntryMatchTapes
end Machine
end RegisterStore
end RAM
end Complexity
end
