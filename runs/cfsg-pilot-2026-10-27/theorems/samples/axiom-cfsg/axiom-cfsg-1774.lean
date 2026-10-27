public noncomputable section

namespace CFSG.Semidihedral.LocalLayerAbelianQuotients

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

open CFSG.Semidihedral.SemilinearOuterQuotient

open CFSG.Semidihedral.SemilinearOddExtensions

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

open CFSG.GorensteinWalter CFSG.Open

open scoped commutatorElement

universe u v

theorem original_odd_inverted_ambient_subgroup_le_layer_preimage
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (W : Subgroup G) (hWC : W ≤ C t) (hW : Odd (Nat.card W)) (a : G) (ha : a ∈ C t)
    (hinv : ∀ w ∈ W, a * w * a⁻¹ = w⁻¹) :
    W ≤ (originalLayerPreimage t).map (C t).subtype := by
  let U := W.subgroupOf (C t)
  have hUodd : Odd (Nat.card U) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]
    exact hW
  have hUinv : ∀ w ∈ U, (⟨a, ha⟩ : C t) * w * (⟨a, ha⟩ : C t)⁻¹ = w⁻¹ := by
    intro w hw
    apply Subtype.ext
    exact hinv w hw
  have hUY : U ≤ originalLayerPreimage t := original_odd_inverted_subgroup_le_layer_preimage
    n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel U hUodd ⟨a, ha⟩ hUinv
  intro w hw
  exact Subgroup.mem_map_of_mem (C t).subtype (hUY (show (⟨w, hWC hw⟩ : C t) ∈ U from hw))

end CFSG.Semidihedral.LocalLayerAbelianQuotients
end
