public section

namespace NFChoice.DirectNominalPrf.Nominal.NFLiteralHandlers

open scoped Fol

open NFChoice.Foundation

open NFChoice.Foundation.ExactLiteralTrial

open NFChoice.SemanticCore

open NFChoice.Compiler.CompactSourceSyntax

/-- Proof-translation construction identified upstream as `axIns3Goal`. -/
@[expose]
def axIns3Goal (x y z w t : Var) : Wff :=
  synWex y
    (.all z (.all w (.all t (synWb
            (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
              (.cv y)) (.classMem (synCopk (.cv z) (.cv w)) (.cv x))))))

end NFChoice.DirectNominalPrf.Nominal.NFLiteralHandlers
end
