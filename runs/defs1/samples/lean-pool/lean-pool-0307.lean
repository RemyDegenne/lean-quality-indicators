@[expose] public section

namespace Complexity

namespace Tape

/-- `t.StartInvariant` says the left-end marker `▷` sits at cell 0 and
    nowhere else — the standing shape of every tape reachable from an
    initial configuration, since writes exclude `▷` and cell 0 is
    immutable. -/
def StartInvariant (t : Tape) : Prop :=
  t.cells 0 = Γ.start ∧ ∀ j, 1 ≤ j → t.cells j ≠ Γ.start

end Tape
end Complexity
end
