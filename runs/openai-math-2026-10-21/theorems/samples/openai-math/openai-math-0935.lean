namespace OAI

open Erdos970

noncomputable section

namespace Ostmann.Construction

open Filter

theorem exists_balanced_pair_centers (d : Decomposition) (a b ρ : ℝ)
    (hρ : 0<ρ) (ha : 0<a/2-ρ) :
    ∀ᶠ L : ℝ in atTop, ∀ T : ℤ,
      a*favorableBlockWidth L≤(T:ℝ) → (T:ℝ)≤b*favorableBlockWidth L →
      ∃u v : ℤ,u+v=T ∧ |(u:ℝ)-(T:ℝ)/2|≤ρ*favorableBlockWidth L ∧
        |(v:ℝ)-(T:ℝ)/2|≤ρ*favorableBlockWidth L ∧
        BalancedCellAfterTwo d u ∧ BalancedCellAfterTwo d v := by
  filter_upwards [eventually_center_window_budget d hρ,
    eventually_good_center_in_window d 2 a b ρ (by norm_num) ha] with L hbudget hgood
  intro T hTlo hThi
  let K := integerCenterWindow ((T:ℝ)/2) (ρ*favorableBlockWidth L)
  let B := badLogCellCenters d (cellPrimeCutoff L) K (1/8)
  have hb := hbudget K
  have hc0 : 0≤(B.card:ℝ) := Nat.cast_nonneg _
  have hb' : 2*(B.card:ℝ)+2≤ρ*favorableBlockWidth L := by change 4*(B.card:ℝ)+4≤_ at hb; linarith
  obtain ⟨u,v,hu,hv,hsum,hub,hvb⟩ := exists_pair_integer_centers B T (ρ*favorableBlockWidth L) hb'
  refine ⟨u,v,hsum,hub,hvb,?_,?_⟩
  · exact hgood T hTlo hThi u ((mem_integerCenterWindow _ _ _).mpr hub) hu
  · exact hgood T hTlo hThi v ((mem_integerCenterWindow _ _ _).mpr hvb) hv

end Ostmann.Construction
end
end OAI
