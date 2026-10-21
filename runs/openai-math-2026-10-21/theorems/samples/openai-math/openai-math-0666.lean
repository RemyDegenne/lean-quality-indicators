namespace OAI

section

noncomputable section

open scoped BigOperators

namespace SharpTerminalLeave

open Classical

theorem densityEdgeSafe_intact_step {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (_hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (h : densityEdgeSafe n p η G) (F : Graph n) :
    pmfMean (step G) (intact F) ≤ Real.exp
      (-((F.card : ℝ)*(6/(n : ℝ)^2/p))+2*(F.card : ℝ)*η*(6/(n : ℝ)^2/p)+
        (F.card : ℝ)^2*(2*(6/(n : ℝ)^2)/(n*p^3))) * intact F G := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ := densityEdgeSafe_triangle_positive hn hp hη1 h
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hQ.card_pos
  obtain ⟨hlo,hhi⟩ := densityEdgeSafe_triangle_bounds h
  let Q₀ : ℝ := (n : ℝ)^3*p^3/6
  let lam : ℝ := 6/(n : ℝ)^2/p
  let D : ℝ := n*p^2
  have hQ₀ : 0 < Q₀ := by dsimp [Q₀]; positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hlamQ : lam*Q₀ = D := by dsimp [lam,Q₀,D]; field_simp
  have hQl : Q₀/2 ≤ (triangles G).card := by
    have hm := mul_le_mul_of_nonneg_left hη1 hQ₀.le
    dsimp only [Q₀] at hm ⊢
    nlinarith only [hlo,hm]
  have hrec : 1/(triangles G).card ≤ 2*(6/(n : ℝ)^2)/(n*p^3) := by
    have hr : 1/(triangles G).card ≤ 2/Q₀ := by
      apply (div_le_div_iff₀ hq hQ₀).mpr
      linarith only [hQl]
    have he : 2/Q₀ = 2*(6/(n : ℝ)^2)/(n*p^3) := by dsimp [Q₀]; field_simp
    rwa [he] at hr
  have hlin : lam*(1-2*η) ≤ D*(1-η)/(triangles G).card := by
    apply (le_div_iff₀ hq).mpr
    have hh : lam*(triangles G).card ≤ D*(1+η) := by
      have hmul := mul_le_mul_of_nonneg_left hhi hlam.le
      change lam*(triangles G).card ≤ lam*(Q₀*(1+η)) at hmul
      rwa [← mul_assoc,hlamQ] at hmul
    have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ 1-2*η by linarith)
    have he : (1+η)*(1-2*η) ≤ 1-η := by nlinarith [sq_nonneg η]
    have he' := mul_le_mul_of_nonneg_left he hD.le
    nlinarith only [hm,he']
  have hexp : -((F.card : ℝ)*D-((F.card : ℝ)*(η*D)+(F.card : ℝ)^2))/(triangles G).card ≤
      -((F.card : ℝ)*lam)+2*(F.card : ℝ)*η*lam+
        (F.card : ℝ)^2*(2*(6/(n : ℝ)^2)/(n*p^3)) := by
    have ha := mul_le_mul_of_nonneg_left hlin (Nat.cast_nonneg F.card)
    have hb := mul_le_mul_of_nonneg_left hrec (sq_nonneg (F.card : ℝ))
    simp only [div_eq_mul_inv] at ha hb ⊢
    nlinarith only [ha,hb]
  have hb := triangle_intact_exponential_bound G F D (η*D) hQ h.2.2
  exact hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (intact_nonnegative F G))

end SharpTerminalLeave
end
end
end OAI
