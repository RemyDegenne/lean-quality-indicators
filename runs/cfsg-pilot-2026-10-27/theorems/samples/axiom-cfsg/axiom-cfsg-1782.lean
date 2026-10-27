public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional

open CFSG.LocalAnalysis.EvenBN.Common (CosetData)

open scoped commutatorElement Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamada_5_13_5 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaS₂ d t ⊓ centralizer (yamadaS₂ d t : Set G) = yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₂ d t) 1).map (yamadaS₂ d t).subtype =
        yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₂ d t) 2).map (yamadaS₂ d t).subtype =
        yamadaY₂ d t := by
  have hZ := h.yamadaS₂_center d hK hD
  have hU₁S₂ : yamadaU₁ d t ≤ yamadaS₂ d t := (yamadaU₁_le_yamadaY₂ d t).trans le_sup_right
  have hY₂S₂ : yamadaY₂ d t ≤ yamadaS₂ d t := le_sup_right
  have hmem1 : ∀ x : yamadaS₂ d t,
      x ∈ Subgroup.upperCentralSeries (yamadaS₂ d t) 1 ↔ (x : G) ∈ yamadaU₁ d t := by
    intro x
    rw [Subgroup.upperCentralSeries_one, ← hZ]
    constructor
    · intro hx
      exact ⟨x.2, mem_centralizer_iff.2 fun y hy =>
        congrArg Subtype.val (mem_center_iff.1 hx ⟨y, hy⟩)⟩
    · rintro ⟨-, hc⟩
      exact mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hc y y.2)
  have hmem2 : ∀ x : yamadaS₂ d t,
      x ∈ Subgroup.upperCentralSeries (yamadaS₂ d t) 2 ↔ (x : G) ∈ yamadaY₂ d t := by
    intro x
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
      h.mem_yamadaY₂_iff d hK hD x.2]
    constructor
    · intro hx g hg
      have := (hmem1 _).1 (hx ⟨g, hg⟩)
      simpa [commutatorElement_def] using this
    · intro hx y
      rw [hmem1]
      simpa [commutatorElement_def] using hx y y.2
  refine ⟨hZ, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem1 y).1 hy
    · intro hx
      exact ⟨⟨x, hU₁S₂ hx⟩, (hmem1 _).2 hx, rfl⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem2 y).1 hy
    · intro hx
      exact ⟨⟨x, hY₂S₂ hx⟩, (hmem2 _).2 hx, rfl⟩

end Local
end Setup
end CFSG.LocalAnalysis.EvenBN.G2
end
