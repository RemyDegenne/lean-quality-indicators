namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section

open scoped Classical BigOperators

open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable {α : Type*} [Fintype α] [DecidableEq α]

variable {b κ n : ℕ}

theorem specifications_probability_le (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (u : Position b → α) (point : Position b → F → Point F)
    (I : Finset (Position b))
    (hinj : ∀ v ∈ I, Function.Injective (point v))
    (hline : ∀ v ∈ I, ∀ t, OnLine (point v t) (lineThrough (a.1 v.1) p))
    (hb : 1 ≤ b) :
    UnusedOffsetIncidence.probability (fun x : α → F =>
      ∃ σ : Fin (3 - κ) → Position b × Code b κ,
        GoodSpecification u I σ ∧ ∀ k,
          PointHolds a p M (fun w => point w (x (u w))) (σ k).1 (σ k).2) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (B : ℝ) / Fintype.card F) ^ (3 - κ) := by
  let E := fun (σ : Fin (3 - κ) → Position b × Code b κ) (x : α → F) =>
    GoodSpecification u I σ ∧ ∀ k,
      PointHolds a p M (fun w => point w (x (u w))) (σ k).1 (σ k).2
  have hE : ∀ σ, UnusedOffsetIncidence.probability (E σ) ≤
      (2 * (B : ℝ) / Fintype.card F) ^ (3 - κ) := by
    intro σ
    by_cases hσ : GoodSpecification u I σ
    · apply (UnusedOffsetIncidence.probability_mono (fun x h => h.2)).trans
      exact specification_product_bound a p M B hB hmult u point I hinj hline
        (⟨0, by omega⟩, 0) σ hσ
    · simp only [E, hσ, false_and, UnusedOffsetIncidence.probability,
        Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  have hsum := (UnusedOffsetIncidence.probability_exists_fintype_le E).trans
    (Finset.sum_le_sum (fun σ _ => hE σ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  apply hsum.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hc := card_specifications_le b κ hb
  have hcr : (Fintype.card (Fin (3 - κ) → Position b × Code b κ) : ℝ) ≤
      (148 * (b : ℝ) ^ 3) ^ 3 := by exact_mod_cast hc
  calc
    _ ≤ (148 * (b : ℝ) ^ 3) ^ 3 := hcr
    _ = (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 := by ring

end
end Balanced.Local.ConditionSpec
end OAI
