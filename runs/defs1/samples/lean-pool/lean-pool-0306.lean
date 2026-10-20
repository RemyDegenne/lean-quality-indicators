@[expose] public section

namespace Circuit

namespace BelnapLevel

/-- The information ordering on Belnap levels: `⊥` is below everything, everything is below `⊤`,
and the two classical values are only related to themselves. -/
@[inline]
def le : BelnapLevel → BelnapLevel → Prop
  | ⊥, _ => true
  | _, ⊤ => true
  | .some (.some x), .some (.some y) => x == y
  | _, _ => false

end BelnapLevel
end Circuit
end
