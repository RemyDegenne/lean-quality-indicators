public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_elimhyp3v`. -/
@[expose]
noncomputable def gElimhyp3v (ph : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff)
    (ze : Wff) (si : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class)
    (hyp_elimhyp3v_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A D)) (synWb ph ch)))
    (hyp_elimhyp3v_2 : Nominal.NPrf (.imp (.classEq B (synCif ph B R)) (synWb ch th)))
    (hyp_elimhyp3v_3 : Nominal.NPrf (.imp (.classEq C (synCif ph C S)) (synWb th ta)))
    (hyp_elimhyp3v_4 : Nominal.NPrf (.imp (.classEq D (synCif ph A D)) (synWb et ze)))
    (hyp_elimhyp3v_5 : Nominal.NPrf (.imp (.classEq R (synCif ph B R)) (synWb ze si)))
    (hyp_elimhyp3v_6 : Nominal.NPrf (.imp (.classEq S (synCif ph C S)) (synWb si ta)))
    (hyp_elimhyp3v_7 : Nominal.NPrf et) : Nominal.NPrf ta :=
  by
  have p0000 := @gIftrue ph A D
  have p0001 := @gEqcomd ph (synCif ph A D) A p0000
  have p0002 :=
    @gSyl ph (.classEq A (synCif ph A D)) (synWb ph ch) p0001 hyp_elimhyp3v_1
  have p0003 := @gIftrue ph B R
  have p0004 := @gEqcomd ph (synCif ph B R) B p0003
  have p0005 :=
    @gSyl ph (.classEq B (synCif ph B R)) (synWb ch th) p0004 hyp_elimhyp3v_2
  have p0006 := @gIftrue ph C S
  have p0007 := @gEqcomd ph (synCif ph C S) C p0006
  have p0008 :=
    @gSyl ph (.classEq C (synCif ph C S)) (synWb th ta) p0007 hyp_elimhyp3v_3
  have p0009 := @gN3bitrd ph ph ch th ta p0002 p0005 p0008
  have p0010 := @gIbi ph ta p0009
  have p0011 := @gIffalse ph A D
  have p0012 := @gEqcomd (.neg ph) (synCif ph A D) D p0011
  have p0013 :=
    @gSyl (.neg ph) (.classEq D (synCif ph A D)) (synWb et ze) p0012 hyp_elimhyp3v_4
  have p0014 := @gIffalse ph B R
  have p0015 := @gEqcomd (.neg ph) (synCif ph B R) R p0014
  have p0016 :=
    @gSyl (.neg ph) (.classEq R (synCif ph B R)) (synWb ze si) p0015 hyp_elimhyp3v_5
  have p0017 := @gIffalse ph C S
  have p0018 := @gEqcomd (.neg ph) (synCif ph C S) S p0017
  have p0019 :=
    @gSyl (.neg ph) (.classEq S (synCif ph C S)) (synWb si ta) p0018 hyp_elimhyp3v_6
  have p0020 := @gN3bitrd (.neg ph) et ze si ta p0013 p0016 p0019
  have p0021 := @gMpbii (.neg ph) et ta hyp_elimhyp3v_7 p0020
  have p0022 := @gPm261i ph ta p0010 p0021
  exact p0022

end NFChoice.DirectNominalPrf.WPPReplay
end
