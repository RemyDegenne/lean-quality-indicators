public section

noncomputable section

open InnerProductSpace Filter

namespace TauCeti

namespace IsPositiveDefiniteSub

variable {G : Type*} [AddCommGroup G] {F : G → ℂ} (hF : IsPositiveDefiniteSub F)

theorem gnsRepresentation_gnsVector (g a : G) :
    hF.gnsRepresentation (Multiplicative.ofAdd g) (hF.gnsVector a) =
      hF.gnsVector (g + a) :=
  by simpa only [hF.gnsRepresentation_ofAdd] using hF.gnsTranslation_gnsVector g a

end IsPositiveDefiniteSub
end TauCeti
end
end
