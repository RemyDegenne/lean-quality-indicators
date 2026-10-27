namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

namespace LBA

section TorusPoints

variable (S : Type) [CommRing S] (t : ℕ)

variable {S t}

noncomputable def convInv (χ : WithConv (torusCoord S t →ₐ[S] S)) : WithConv (torusCoord S t →ₐ[S] S) :=
  WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S (-AddMonoidHom.id (Fin t → ℤ))))

end TorusPoints
end LBA
end P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le
