namespace OAI

noncomputable section

open scoped BigOperators

open Finset

open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem

open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration

open Finset Classical

variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma center_empty_lit_pointwise (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (p : S.Index) (hc : ¬S.IsCore p)
    (hocc : (treeOccurrences w p).Nonempty) (a : ZMod (p : ℕ))
    (hE : litEdges w p a = ∅) :
    |localWithList w 𝔏 p a| * allPrimeCharges w U p a ≤ theta / (p : ℝ) := by
  obtain ⟨e,he⟩ := hocc
  have het := (mem_filter.mp he).1
  have hed := (mem_filter.mp he).2
  have hea : a + (w.offset e.castSucc : ZMod (p : ℕ)) ≠ 0 := by
    intro ha
    have hm : e ∈ litEdges w p a := mem_filter.mpr ⟨he,ha⟩
    simp [hE] at hm
  have ho (i : Fin ℓ) (hi : i ∈ w.treeSteps) : |S.occurrenceFactor w p i a| ≤ 1 := by
    have hh := occurrence_abs_le_lit_amplitude w p a i hi
    simpa only [amplitude, hc, ite_false, ite_self] using hh
  have hop : (∏ i ∈ w.treeSteps, |S.occurrenceFactor w p i a|) ≤ theta / (p : ℝ) := by
    calc
      _ ≤ ∏ i ∈ ({e} : Finset (Fin ℓ)), |S.occurrenceFactor w p i a| :=
        prod_le_prod_of_subset_of_le_one₀ (singleton_subset_iff.mpr het)
          (fun _ _ => abs_nonneg _) (fun i hi _ => ho i hi)
      _ = _ := by
        simp only [prod_singleton, occurrenceFactor, hed, hc, ite_true, ite_false,
          activity, ite_eq_right hea, zero_sub, abs_neg, abs_of_nonneg (theta_div_bounds p).1]
  have htop : NoComponentTop w U p (litEdges w p a) := fun h => (hc h).elim
  have hn := tree_norm_charges_le w U hU p a htop
  rw [hE] at hn
  simp only [edgeVertices, image_empty, union_self, prod_empty] at hn
  calc
    _ ≤ |S.primeFactor w p a| * allPrimeCharges w U p a := charged_local_le w 𝔏 U p a
    _ ≤ _ := charged_prime_le_tree w U p a
    _ ≤ (theta / (p : ℝ)) * 1 := mul_le_mul hop hn
      (mul_nonneg (prod_nonneg (fun _ _ => pow_nonneg (beta_nonneg p) _))
        (prod_nonneg (fun _ _ => primeCharge_nonneg _ _ _ _))) (theta_div_bounds p).1
    _ = _ := mul_one _

end OrdinaryCorrelations.GraphKernel.PrimeSystem
end
end OAI
