public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_rexanali`. -/
@[expose]
noncomputable def gRexanali (ph : Wff) (ps : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (synWb (synWrex x A (synWa ph (.neg ps))) (.neg (synWral x A (.imp ph ps)))) :=
  by
  have p0000 := @gAnnim ph ps
  have p0001 := @gRexbii (synWa ph (.neg ps)) (.neg (.imp ph ps)) x A p0000
  have p0002 := @gRexnal (.imp ph ps) x A
  have p0003 :=
    @gBitri (synWrex x A (synWa ph (.neg ps))) (synWrex x A (.neg (.imp ph ps)))
      (.neg (synWral x A (.imp ph ps))) p0001 p0002
  exact p0003

end NFChoice.DirectNominalPrf.WPPReplay
end
