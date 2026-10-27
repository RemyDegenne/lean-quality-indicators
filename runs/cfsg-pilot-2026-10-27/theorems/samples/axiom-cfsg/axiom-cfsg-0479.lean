public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace S715L

open S714

variable [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem false_of_isLayerConfigC (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h51 : Stroth51Statement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement) (hCRW : Sec7CRWStatement)
    (hMp : Sec7CentreMpStatement) (hY : Sec713YStatement) (hCent : Sec715CentStatement)
    (hConj : Sec715ConjStatement) (hS : IsTensorSetup hc n M₀ ρ b) {t r : G}
    (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4) (hn : n = 16)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    (hC : IsLayerConfigC hS hs.toSec5.mem) : False := by
  obtain ⟨M₃, M₄, N₄, N₃, hM, hN, h₄, h₃, hpres, hM34, hβ, hc5, hT⟩ := hC
  exact configC_false h34 h310chi h51 h52a hA hZt hZcard hZc hZV hCommN hCRW hMp hY hCent hConj
    hS hs hr hp hn hZ0 hZN hTI hSΔ hM hN h₄ h₃ hpres hM34 hβ hc5 hT

end S715L
end CFSG.RankThree.GF2n.Stroth80
end
