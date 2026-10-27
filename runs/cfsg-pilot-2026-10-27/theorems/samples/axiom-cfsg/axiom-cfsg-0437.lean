public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.LocalAnalysis.ComponentInitial

open CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models.OrthogonalPairs

open CFSG.SeitzReduction.UnitaryPilot (permSUHom)

section Charts

variable {G : Type} [Group G] {p f : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
  [Finite K] [CharP K 2] {E : QuadExt F K (unitaryInvolution K 2 f)}

theorem uniFourChart_map_normBlock_eq_uniFourBlocks [Finite G] [Fact p.Prime]
    {Bs L KU : Subgroup G} {x : G} {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin 4)} {κ : normOmega E 3 →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (hK : UnitaryFieldData 2 f K)
    {σ : ↥(unitarySU 2 f K 4) →* G} {χ' : Multiplicative (ZMod p) →* Kˣ}
    (hσ : GGSecFiveBPermUniLFrame Bs KU eta π σ χ')
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hA : (ggAutomizer KU Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 4 p)
    (hX : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G))) (hxB : x ∈ Bs)
    (hpq : p ∣ 2 ^ f + 1) (i : Fin 4) (S : Finset (Fin 3)) (hS : S.Nonempty)
    (hS2 : S.card ≤ 2) :
    (normBlock E 3 S).map (uniFourChart hK σ κ i) =
      uniFourBlocks Bs eta π (S.image i.succAbove) := by
  exact fourCharts_map_normBlock_eq_uniFourBlocks (uniFourChart hK σ κ)
    (fun i s t hst => uniFourChart_map_normBlock_singleton hκ hK hσ hBsC hA hX hxB hpq i hst)
    (fun i s t hst => uniFourChart_map_normBlock_pair hκ hK hσ hBsC hA hX hxB i hst)
    i S hS hS2

end Charts
end CFSG.StandardType
end
