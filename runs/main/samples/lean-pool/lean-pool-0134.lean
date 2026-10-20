@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

namespace EntryLookupRestoreTapes

theorem scan_ne_external {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    (slot : Fin 10) (external : Fin 4) :
    tapes.idx ⟨slot.val, by omega⟩ ≠
      tapes.idx ⟨external.val + 10, by omega⟩ := by
  apply tapes.ne
  intro h
  have hval := congrArg Fin.val h
  change slot.val = external.val + 10 at hval
  omega

end EntryLookupRestoreTapes
end Machine
end RegisterStore
end RAM
end Complexity
end
