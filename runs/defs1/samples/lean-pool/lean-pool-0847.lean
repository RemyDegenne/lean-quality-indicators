public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_eqtr3d`. -/
@[expose]
noncomputable def gEqtr3d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqtr3d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqtr3d_2 : Nominal.NPrf (.imp ph (.classEq A C))) :
    Nominal.NPrf (.imp ph (.classEq B C)) :=
  by
  have p0000 := @gEqcomd ph A B hyp_eqtr3d_1
  have p0001 := @gEqtrd ph B A C p0000 hyp_eqtr3d_2
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
