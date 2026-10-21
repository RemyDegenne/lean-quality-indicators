namespace OAI

noncomputable section

namespace KadisonSimilarity

open ContinuousLinearMap

open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem boundedHom_vector_states (lg : LittleGrothendieckInput A H)
    (π : BoundedUnitalHom A H) {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) (ξ : H) :
    ∃ f g : A →ₚ[ℂ] ℂ, (f 1).re ≤ 1 ∧ (g 1).re ≤ 1 ∧
      ∀ a, ‖(π.1 a).adjoint ξ‖ ^ 2 ≤
        M ^ 4 * ‖ξ‖ ^ 2 * ((f (a * star a)).re + (g (a * star a)).re) := by
  obtain ⟨f, g, hf, hg, hfg⟩ := lg (sharpVectorMap π ξ)
  refine ⟨f, g, hf, hg, ?_⟩
  intro a
  let h := CFC.sqrt (a * star a)
  have hh : 0 ≤ h := CFC.sqrt_nonneg _
  have hsq : h * h = a * star a := CFC.sqrt_mul_sqrt_self _ (mul_star_self_nonneg a)
  have hp := hom_adjoint_sqrt_bound π hM hπ a ξ
  change ‖(π.1 a).adjoint ξ‖ ≤ M * ‖(π.1 h).adjoint ξ‖ at hp
  have hl := hfg h
  simp only [sharpVectorMap_apply, hh.star_eq, hsq] at hl
  have hpos : 0 ≤ (f (a * star a)).re + (g (a * star a)).re :=
    add_nonneg (f.map_nonneg (mul_star_self_nonneg a)).1
      (g.map_nonneg (mul_star_self_nonneg a)).1
  calc
    _ ≤ (M * ‖(π.1 h).adjoint ξ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
    _ = M ^ 2 * ‖(π.1 h).adjoint ξ‖ ^ 2 := by ring
    _ ≤ M ^ 2 * (‖sharpVectorMap π ξ‖ ^ 2 *
        ((f (a * star a)).re + (g (a * star a)).re)) := mul_le_mul_of_nonneg_left hl (sq_nonneg M)
    _ ≤ M ^ 2 * ((M * ‖ξ‖) ^ 2 * ((f (a * star a)).re + (g (a * star a)).re)) := by
      gcongr
      exact norm_sharpVectorMap_le_general π hM hπ ξ
    _ = _ := by ring

end KadisonSimilarity
end
end OAI
