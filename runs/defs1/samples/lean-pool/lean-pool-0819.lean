public section

namespace NFChoice.Compiler.CompactSourceSyntax

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

/-- Compact nominal syntax for the upstream `cfin` operator. -/
@[expose]
def synCfin : Class :=
  (synCuni (synCnnc))

end NFChoice.Compiler.CompactSourceSyntax
end
