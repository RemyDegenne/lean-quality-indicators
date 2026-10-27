public noncomputable section

namespace CFSG.StandardType.E8PowerWNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.StandardType.TableBExc

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTorusWNormSC_recipe_E8_of_powerMap {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hS : SylowTorus (adjointGroup .E8 K) p 4) {k : ℕ}
    (hV : ∃ V : Subgroup (adjointGroup .E8 K), IsElemAbelian p V ∧ Nat.card V = p ^ 4 ∧
      ∃ y : adjointGroup .E8 K, ∀ x ∈ V, y * x * y⁻¹ = x ^ k)
    (hk : ((k : ZMod p)) ^ 8 ≠ 1) :
    GGTorusWNormSC p (RecipeGroup .E8 K) (RecipeID .E8 K) := by
  classical
  intro L _ _ ψ hψ hker hperf A hA hAI _ hsc _ Γ _ _ M C W _ _ ι φ h α _ hC hα hφ hgen φ' _
  exfalso
  obtain ⟨hAcard, φ₀, hφ₀, hφ₀k⟩ :=
    exists_powerMap_mem_automizer_E8 hp hp2 hS hV ψ hψ hker hperf hA hAI hsc
  have hAfin : Finite A :=
    Nat.finite_of_card_ne_zero (by rw [hAcard]; exact (pow_pos hp.pos 4).ne')
  rw [hgen] at hφ₀
  have hsq := ggLin_det_sq_eq_one_of_mem_closure_refl ι φ h α
    (fun i => by rw [hα i i, hC.1 i]; norm_num) hφ hφ₀
  have hdet := ggLin_det_of_pow (p := p) ι hφ₀k
  have hWfin : Finite W := Finite.of_equiv _ ι.toEquiv
  have hrank : Module.finrank (ZMod p) W = 4 := by
    have h1 := FiniteField.pow_finrank_eq_natCard p W
    rw [← Nat.card_congr ι.toEquiv, Nat.card_congr Additive.toMul, hAcard] at h1
    exact Nat.pow_right_injective hp.two_le h1
  apply hk
  have h2 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hsq
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
  rw [hdet, hrank, ← pow_mul] at h2
  exact h2

end CFSG.StandardType.E8PowerWNorm
end
