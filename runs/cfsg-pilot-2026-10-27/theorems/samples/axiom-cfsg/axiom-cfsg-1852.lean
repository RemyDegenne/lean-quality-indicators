public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem betaGL_rootDiagUnit (a : Fin Tag.E6.rank → Kˣ) :
    betaGL (rootDiagUnit Tag.E6 a) =
      rootDiagUnit Tag.E6 fun i => Units.map barHom.toMonoidHom (a i) :=
  Units.ext (entrywise_rootDiag barHom a)

end CFSG.LieType.Chevalley.C2E6Std
end
