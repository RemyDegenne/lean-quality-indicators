@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

theorem EntryScanReady.cleanup_target_head_eq_one_internal
    {tapes : EntryMatchTapes n} {remaining queryBits : List Bool}
    {initialWork work : Fin n → Tape}
    (h : EntryScanReady tapes remaining queryBits initialWork work) :
    ∀ i, i ∈ entryMissTargets tapes → (work i).head = 1 := by
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · simpa using h.address.1
  · simpa using h.value.1
  · exact h.addressCounter.2.1
  · exact h.addressWidth.2.1
  · exact h.valueCounter.2.1
  · exact h.valueWidth.2.1
  · simpa using h.result.1

end Machine
end RegisterStore
end RAM
end Complexity
end
