public section

open Subgroup

open scoped commutatorElement

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_L54 [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {Y₀ : Subgroup G} (hY1 : Y₀ ≠ ⊥) (hYZ : Y₀ ≤ centralizer ((layerOf x : Subgroup G) : Set G))
    (hcase : IsSylowOf p (frU P x) (normalizer (Y₀ : Set G)) ∨ x ∈ normalizer (Y₀ : Set G))
    {W : Subgroup G} (hWp : Nat.Coprime p (Nat.card W)) (hWN : W ≤ normalizer (Y₀ : Set G))
    (hUW : frU P x ≤ normalizer (W : Set G)) :
    W ≤ centralizer ((layerOf x : Subgroup G) : Set G) := by
  obtain ⟨hNtop, hLN⟩ := fr_normalizer_ne_top hG hl hY1 hYZ
  exact fr_L54_N hK hG hl hNtop hLN hcase hWp hWN hUW

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
end
