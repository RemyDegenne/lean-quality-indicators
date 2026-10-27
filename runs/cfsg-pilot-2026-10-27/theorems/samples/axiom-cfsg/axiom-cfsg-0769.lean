public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
  CFSG.ComponentClassification.OddSelector CFSG CFSG.GH74 CFSG.GH74.GLS

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace PuL4GraphLin

theorem rhoOf_injective {N : Type*} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {P : Type*} [Group P] (e : ↥H ≃* P) :
    Function.Injective (rhoOf e) :=
  GenLocL4Refl.injective_congr_conjNormal hfaith e

end PuL4GraphLin
end CFSG.GH74.Generic.BProg.B2
end
