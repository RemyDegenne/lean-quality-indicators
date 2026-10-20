@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

/-- Maximum address/value bit-width materialized in a sparse store. -/
def maxWidth : Store → ℕ
  | [] => 0
  | entry :: rest =>
      max (bitlen entry.1) (max (bitlen entry.2) (maxWidth rest))

end RegisterStore
end RAM
end Complexity
end
