public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary Subgroup

open CFSG.LieType.Universal.Unitary (SUid)

section Torus

variable {F : Type} [Field F] (σ : F ≃+* F)

variable {σ}

theorem torusSU_smul (Z : Subgroup Fˣ) (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) (x : ↥Z × ↥Z)
    (v : Fin 4 → F) :
    torusSU Z hZ x • v = fun i => torusVec (x.1 : Fˣ) (x.2 : Fˣ) i * v i :=
  diagSU_smul σ _ (torusVec_norm hZ x.1.2 x.2.2) (torusVec_det _ _) v

end Torus
end CFSG.LocalAnalysis.RankThreeUC
end
