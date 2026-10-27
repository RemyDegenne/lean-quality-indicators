public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP

open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour CFSG.Quasithin.JonesParshall

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

open scoped commutatorElement Matrix

section Alg

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem cform_add (B B' : F) (m m' : V4 F) (g : Sp4 F) :
    S5.cform (B + B') (m + m') g = S5.cform B m g + S5.cform B' m' g := by
  simp only [S5.cform, add_smul, Matrix.mulVec_add]
  abel

end Alg
end CFSG.Quasithin.MS93.S37
end
