@[expose] public section

universe u v w

namespace MvPolynomial

theorem mem_map_C_sup_span_X_image_iff
    {σ : Type u} {R : Type v} [CommSemiring R]
    {I : Ideal R} {S : Set σ} {p : MvPolynomial σ R} :
    p ∈ Ideal.map (C : R →+* MvPolynomial σ R) I ⊔
      Ideal.span ((X : σ → MvPolynomial σ R) '' S) ↔
        ∀ d : σ →₀ ℕ, (∀ i ∈ S, d i = 0) → p.coeff d ∈ I := by
  classical
  constructor
  · intro hp
    rcases Submodule.mem_sup.mp hp with ⟨a, ha, b, hb, rfl⟩
    intro d hd
    have hbzero : b.coeff d = 0 := by
      by_contra hne
      obtain ⟨i, hi, hdi⟩ := mem_ideal_span_X_image.mp hb d (mem_support_iff.mpr hne)
      exact hdi (hd i hi)
    simpa [hbzero] using mem_map_C_iff_coeff_mem.mp ha d
  · intro hp
    rw [p.as_sum]
    refine Ideal.sum_mem _ fun d _ => ?_
    by_cases hd : ∀ i ∈ S, d i = 0
    · apply Submodule.mem_sup_left
      have hC : C (p.coeff d) ∈ Ideal.map (C : R →+* MvPolynomial σ R) I :=
        Ideal.mem_map_of_mem C (hp d hd)
      simpa only [C_mul_monomial, mul_one] using
        (Ideal.map (C : R →+* MvPolynomial σ R) I).mul_mem_right (monomial d 1) hC
    · apply Submodule.mem_sup_right
      simp only [not_forall] at hd
      obtain ⟨i, hi, hdi⟩ := hd
      apply mem_ideal_span_X_image.mpr
      intro m hm
      have hmd : m = d := Finset.mem_singleton.mp (support_monomial_subset hm)
      exact ⟨i, hi, hmd.symm ▸ hdi⟩

end MvPolynomial
end
