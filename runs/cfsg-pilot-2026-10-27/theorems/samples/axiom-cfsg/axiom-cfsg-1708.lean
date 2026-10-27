public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

open scoped Matrix

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4

namespace TypeIIData

variable {F : Type} [Field F] {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} {d : F}
  (h : TypeIIData A d)

include h

theorem ωJ_sim (x y : Fin 2 ⊕ Fin 2 → F) : ωJ F (A *ᵥ x) (A *ᵥ y) = d * ωJ F x y :=
  ωJ_similitude h.sim x y

end TypeIIData
end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
end
