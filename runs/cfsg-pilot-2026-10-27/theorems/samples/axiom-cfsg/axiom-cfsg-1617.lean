public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2

open CFSG.RankThree.Lattice (e6T3W)

open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)

variable {L : Type} [Field L] {Fr : L →+* L}

theorem twistedFixedPoints_phi3N :
    twistedFixedPoints (phi3N L) (Units.map (entrywiseHom Fr)) =
      (phi3Theta L Fr).eqLocus (MonoidHom.id _) :=
  rfl

end CFSG.RankThree.PartOne.KE6
end
