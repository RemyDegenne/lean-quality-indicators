public section

namespace NFChoice.Compiler.CompactSourceSyntax

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

/-- Compact nominal syntax for the upstream `cphi` operator. -/
@[expose]
def synCphi (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (.cab y (synWrex x A (.classEq (.cv y)
        (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x)))))

end NFChoice.Compiler.CompactSourceSyntax
end
