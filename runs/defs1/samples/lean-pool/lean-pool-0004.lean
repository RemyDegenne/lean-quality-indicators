public section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol

open NFChoice.Foundation

open NFChoice.Foundation.ExactLiteralTrial

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

open NFChoice.Compiler.CompactSyntaxFVExplicit

open NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Compiler.CoreFVSimp

open NFChoice.DefinitionLeaves.AlphaFocusedSupport

open NFChoice.DefinitionLeaves.AlphaFocusedFV

open NFChoice.DirectNominalPrf

open NFChoice.DirectNominalPrf.Nominal

namespace FirstProjectionAlpha

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_036`. -/
@[expose]
def alphaDummy036 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv y)
            (Wff.classEq (Class.cv (alphaDummy007 x y))
              (synCun (synCphi (Class.cv (alphaDummy008 x y))) (synCsn (synC0c))))))).fv ∪
      ((Class.cab (alphaDummy007 x y) (synWrex (alphaDummy008 x y) (Class.cv y)
            (Wff.classEq (Class.cv (alphaDummy007 x y))
              (synCun (synCphi (Class.cv (alphaDummy008 x y))) (synCsn (synC0c))))))).fv)
    0)

end FirstProjectionAlpha
end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
