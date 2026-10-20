public section

namespace NFChoice.Compiler.CompactSourceSyntax

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

/-- Compact nominal syntax for the upstream `cwpppredfam` operator. -/
@[expose]
def synCwpppredfam (F : Class) (C : Class) : Class :=
  (synCcom (synCimage (synCcnv
        (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)))) (synCimage (synCsset)))

end NFChoice.Compiler.CompactSourceSyntax
end
