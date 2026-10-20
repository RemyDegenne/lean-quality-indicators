@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace ThreeSATSyntax

open SAT.ThreeSAT

/-- Reserved-prefix input store for the syntax scanner. -/
abbrev inputStore : List Bool → Store := spec.inputStore

end ThreeSATSyntax
end Structured
end RAM
end Complexity
end
