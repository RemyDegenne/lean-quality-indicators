public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup DihedralGroup

theorem prop29ConclCorr_of_map {H P : Type} [Group H] [Finite H] [Group P] [Finite P]
    [(generalizedFitting H).Normal] {ι₀ : P} {J : Subgroup P} {m : ℕ} (M : Model ⊤ ι₀ J m)
    (ψ : P →* H) (hψ : Function.Injective ψ) (hL : ψ.range = generalizedFitting H)
    {ι : H} (hι : ψ ι₀ = ι) {J₁ : Subgroup H} (hJ : J.map ψ = J₁) (hO : pPrimeCore 2 ↥J₁ = ⊥)
    {S₁ : Subgroup H} (hS : Seven.IsSylowIn S₁ (centralizer ({ι} : Set H))) :
    Prop29ConclCorr H ι J₁ S₁ :=
  prop29ConclCorr_of_model (M.map ψ hψ hL hι hJ) hO hS

end CFSG.ComponentClassification.GSThmB.P29
end
