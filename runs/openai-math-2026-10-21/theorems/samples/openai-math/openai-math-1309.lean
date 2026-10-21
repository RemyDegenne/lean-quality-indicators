namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma energy_supermodular {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ ρ : Spins n) :
    energy G h σ + energy G h ρ ≤ energy G h (σ ⊓ ρ) + energy G h (σ ⊔ ρ) := by
  have he : (∑ e, (G.coupling e * spin (σ (G.left e)) * spin (σ (G.right e)) +
      G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e)))) ≤
      ∑ e, (G.coupling e * spin ((σ ⊓ ρ) (G.left e)) * spin ((σ ⊓ ρ) (G.right e)) +
      G.coupling e * spin ((σ ⊔ ρ) (G.left e)) * spin ((σ ⊔ ρ) (G.right e))) := by
    apply Finset.sum_le_sum
    intro e _
    have H := mul_le_mul_of_nonneg_left
      (spin_product_supermodular (σ (G.left e)) (σ (G.right e))
        (ρ (G.left e)) (ρ (G.right e))) (G.coupling_nonneg e)
    simpa only [Pi.inf_apply, Pi.sup_apply, mul_add, mul_assoc] using H
  have hv : (∑ v, (h v * spin (σ v) + h v * spin (ρ v))) =
      ∑ v, (h v * spin ((σ ⊓ ρ) v) + h v * spin ((σ ⊔ ρ) v)) := by
    apply Finset.sum_congr rfl
    intro v _
    simpa only [Pi.inf_apply, Pi.sup_apply, mul_add] using
      congrArg (fun x => h v * x) (spin_modular (σ v) (ρ v))
  dsimp [energy]
  simp only [Finset.sum_add_distrib] at he hv
  dsimp at he hv
  linarith

end BufferedIsing
end OAI
