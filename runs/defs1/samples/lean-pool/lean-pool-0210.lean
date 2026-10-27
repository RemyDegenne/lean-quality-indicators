public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr3d`. -/
@[expose]
noncomputable def gN3bitr3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr3d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_n_3bitr3d_2 : Nominal.NPrf (.imp ph (synWb ps th)))
    (hyp_n_3bitr3d_3 : Nominal.NPrf (.imp ph (synWb ch ta))) :
    Nominal.NPrf (.imp ph (synWb th ta)) :=
  by
  have p0000 := @gBitr3d ph ps th ch hyp_n_3bitr3d_2 hyp_n_3bitr3d_1
  have p0001 := @gBitrd ph th ch ta p0000 hyp_n_3bitr3d_3
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
