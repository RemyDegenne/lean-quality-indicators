public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem false_of_extremal_fused {j k : Fin 9}
    (hj : IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({D.toG (SE.invRep j)} : Set G))
      (centralizer ({D.toG (SE.invRep j)} : Set G)))
    (hlt : SE.invRepCent j < SE.invRepCent k) (h : D.FusN j k) : False :=
  (D.not_fusN_of_lt hj hlt).1 h

end GHSylow
end CFSG.ComponentClassification.GHarris
end
