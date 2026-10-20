namespace P2MW.S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition

set_option autoImplicit false

namespace KSpec

noncomputable section

section SO3

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem cube_eq_neg (F : Submodule ℂ V) [FiniteDimensional ℂ F] (J₁ J₂ J₃ : Module.End ℂ V)
    (hF₁ : ∀ f ∈ F, J₁ f ∈ F) (hF₂ : ∀ f ∈ F, J₂ f ∈ F) (hF₃ : ∀ f ∈ F, J₃ f ∈ F)
    (h12 : ∀ f ∈ F, J₁ (J₂ f) - J₂ (J₁ f) = J₃ f)
    (h23 : ∀ f ∈ F, J₂ (J₃ f) - J₃ (J₂ f) = J₁ f)
    (h31 : ∀ f ∈ F, J₃ (J₁ f) - J₁ (J₃ f) = J₂ f)
    (hcas : ∀ f ∈ F, J₁ (J₁ f) + J₂ (J₂ f) + J₃ (J₃ f) = (-2 : ℂ) • f)
    (B : V → V → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ F, ∀ w₂ ∈ F, ∀ w' ∈ F, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ F, ∀ w' ∈ F, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ F, w ≠ 0 → 0 < (B w w).re)
    (hskew₁ : ∀ x ∈ F, ∀ y ∈ F, B (J₁ x) y = -B x (J₁ y))
    (hskew₂ : ∀ x ∈ F, ∀ y ∈ F, B (J₂ x) y = -B x (J₂ y))
    (hskew₃ : ∀ x ∈ F, ∀ y ∈ F, B (J₃ x) y = -B x (J₃ y)) :
    ∀ f ∈ F, J₃ (J₃ (J₃ f)) = -J₃ f := by
  classical

  have hB0 : ∀ y ∈ F, B 0 y = 0 := fun y hy => form_zero_left F B hlin hy
  have hBsmul : ∀ (z : ℂ), ∀ x ∈ F, ∀ y ∈ F, B (z • x) y = z * B x y := fun z x hx y hy => by
    have h := hlin z x hx 0 F.zero_mem y hy
    rw [add_zero, hB0 y hy, add_zero] at h; exact h
  have hBadd : ∀ x₁ ∈ F, ∀ x₂ ∈ F, ∀ y ∈ F, B (x₁ + x₂) y = B x₁ y + B x₂ y := fun x₁ h₁ x₂ h₂ y hy => by
    have h := hlin 1 x₁ h₁ x₂ h₂ y hy
    rw [one_smul, one_mul] at h; exact h
  have hBsub : ∀ x₁ ∈ F, ∀ x₂ ∈ F, ∀ y ∈ F, B (x₁ - x₂) y = B x₁ y - B x₂ y := fun x₁ h₁ x₂ h₂ y hy => by
    have h := hlin (-1) x₂ h₂ x₁ h₁ y hy
    rw [neg_one_smul, neg_add_eq_sub] at h; rw [h]; ring
  have hBsmul' : ∀ (z : ℂ), ∀ x ∈ F, ∀ y ∈ F, B x (z • y) = (starRingEnd ℂ) z * B x y := fun z x hx y hy => by
    rw [hsymm _ (F.smul_mem z hy) x hx, hBsmul z y hy x hx, map_mul, ← hsymm y hy x hx]
  have hBadd' : ∀ x ∈ F, ∀ y₁ ∈ F, ∀ y₂ ∈ F, B x (y₁ + y₂) = B x y₁ + B x y₂ := fun x hx y₁ h₁ y₂ h₂ => by
    rw [hsymm _ (F.add_mem h₁ h₂) x hx, hBadd y₁ h₁ y₂ h₂ x hx, map_add, ← hsymm y₁ h₁ x hx, ← hsymm y₂ h₂ x hx]
  have hBsub' : ∀ x ∈ F, ∀ y₁ ∈ F, ∀ y₂ ∈ F, B x (y₁ - y₂) = B x y₁ - B x y₂ := fun x hx y₁ h₁ y₂ h₂ => by
    rw [hsymm _ (F.sub_mem h₁ h₂) x hx, hBsub y₁ h₁ y₂ h₂ x hx, map_sub, ← hsymm y₁ h₁ x hx, ← hsymm y₂ h₂ x hx]
  have hBself : ∀ w ∈ F, B w w = ((B w w).re : ℂ) := fun w hw => by
    have h := hsymm w hw w hw
    exact (Complex.conj_eq_iff_re.1 h.symm).symm
  have hBre_nonneg : ∀ w ∈ F, 0 ≤ (B w w).re := fun w hw => by
    by_cases h0 : w = 0
    · rw [h0, hB0 0 F.zero_mem]; simp
    · exact (hpos w hw h0).le

  let L : Module.End ℂ V := Complex.I • J₃
  let Xp : Module.End ℂ V := J₁ + Complex.I • J₂
  let Xm : Module.End ℂ V := J₁ - Complex.I • J₂
  have hLF : ∀ f ∈ F, L f ∈ F := fun f hf => F.smul_mem _ (hF₃ f hf)
  have hXpF : ∀ f ∈ F, Xp f ∈ F := fun f hf => F.add_mem (hF₁ f hf) (F.smul_mem _ (hF₂ f hf))
  have hXmF : ∀ f ∈ F, Xm f ∈ F := fun f hf => F.sub_mem (hF₁ f hf) (F.smul_mem _ (hF₂ f hf))
  have hL_apply : ∀ f, L f = Complex.I • J₃ f := fun f => rfl
  have hXp_apply : ∀ f, Xp f = J₁ f + Complex.I • J₂ f := fun f => rfl
  have hXm_apply : ∀ f, Xm f = J₁ f - Complex.I • J₂ f := fun f => rfl

  have hLsymm : ∀ w ∈ F, ∀ w' ∈ F, B (L w) w' = B w (L w') := fun w hw w' hw' => by
    rw [hL_apply, hL_apply, hBsmul _ _ (hF₃ w hw) _ hw', hBsmul' _ _ hw _ (hF₃ w' hw'), hskew₃ w hw w' hw', Complex.conj_I]
    ring

  have hLXp : ∀ f ∈ F, L (Xp f) - Xp (L f) = Xp f := fun f hf => by
    simp only [hL_apply, hXp_apply, map_add, map_smul, smul_add, smul_sub, smul_smul, Complex.I_mul_I]
    have e1 := h31 f hf
    have e2 := h23 f hf

    have e1' : J₃ (J₁ f) = J₂ f + J₁ (J₃ f) := by rw [← e1]; abel
    have e2' : J₃ (J₂ f) = J₂ (J₃ f) - J₁ f := by rw [← e2]; abel
    rw [e1', e2']
    simp only [smul_add, smul_sub, neg_one_smul]
    abel
  have hLXm : ∀ f ∈ F, L (Xm f) - Xm (L f) = -Xm f := fun f hf => by
    simp only [hL_apply, hXm_apply, map_sub, map_smul, smul_sub, smul_smul, Complex.I_mul_I]
    have e1' : J₃ (J₁ f) = J₂ f + J₁ (J₃ f) := by rw [← h31 f hf]; abel
    have e2' : J₃ (J₂ f) = J₂ (J₃ f) - J₁ f := by rw [← h23 f hf]; abel
    rw [e1', e2']
    simp only [smul_add, smul_sub, neg_one_smul, neg_sub]
    abel

  have hJ3L : ∀ f, J₃ f = (-Complex.I) • L f := fun f => by
    rw [hL_apply, smul_smul]; simp
  have hXmXp : ∀ f ∈ F, Xm (Xp f) = L (L f) + L f - (2 : ℂ) • f := fun f hf => by
    have hc := hcas f hf
    simp only [hXm_apply, hXp_apply, map_add, map_smul, smul_add, hL_apply, smul_smul, Complex.I_mul_I]

    have e12 : J₁ (J₂ f) = J₃ f + J₂ (J₁ f) := by rw [← h12 f hf]; abel
    have hJJ : J₁ (J₁ f) + J₂ (J₂ f) = (-2 : ℂ) • f - J₃ (J₃ f) := by rw [← hc]; abel
    rw [e12]
    simp only [smul_add, sub_smul, neg_one_smul]
    linear_combination (norm := module) hJJ
  have hXpXm : ∀ f ∈ F, Xp (Xm f) = L (L f) - L f - (2 : ℂ) • f := fun f hf => by
    have hc := hcas f hf
    simp only [hXm_apply, hXp_apply, map_sub, map_smul, smul_sub, hL_apply, smul_smul, Complex.I_mul_I]
    have e12 : J₁ (J₂ f) = J₃ f + J₂ (J₁ f) := by rw [← h12 f hf]; abel
    have hJJ : J₁ (J₁ f) + J₂ (J₂ f) = (-2 : ℂ) • f - J₃ (J₃ f) := by rw [← hc]; abel
    rw [e12]
    simp only [smul_add, neg_one_smul]
    linear_combination (norm := module) hJJ

  have hadjp : ∀ w ∈ F, ∀ y ∈ F, B (Xp w) y = -B w (Xm y) := fun w hw y hy => by
    rw [hXp_apply, hXm_apply, hBadd _ (hF₁ w hw) _ (F.smul_mem _ (hF₂ w hw)) y hy,
      hBsmul _ _ (hF₂ w hw) y hy, hskew₁ w hw y hy, hskew₂ w hw y hy,
      hBsub' w hw _ (hF₁ y hy) _ (F.smul_mem _ (hF₂ y hy)), hBsmul' _ w hw _ (hF₂ y hy), Complex.conj_I]
    ring
  have hadjm : ∀ w ∈ F, ∀ y ∈ F, B (Xm w) y = -B w (Xp y) := fun w hw y hy => by
    rw [hXp_apply, hXm_apply, hBsub _ (hF₁ w hw) _ (F.smul_mem _ (hF₂ w hw)) y hy,
      hBsmul _ _ (hF₂ w hw) y hy, hskew₁ w hw y hy, hskew₂ w hw y hy,
      hBadd' w hw _ (hF₁ y hy) _ (F.smul_mem _ (hF₂ y hy)), hBsmul' _ w hw _ (hF₂ y hy), Complex.conj_I]
    ring

  have hbound : ∀ w ∈ F, w ≠ 0 → ∀ μ : ℂ, L w = μ • w →
      μ = (μ.re : ℂ) ∧ (μ.re + 2) * (μ.re - 1) ≤ 0 ∧ (μ.re - 2) * (μ.re + 1) ≤ 0 := by
    intro w hw hw0 μ hμ
    have hp : 0 < (B w w).re := hpos w hw hw0

    have hreal : μ = (μ.re : ℂ) := by
      have h1 : B (L w) w = μ * B w w := by rw [hμ, hBsmul μ w hw w hw]
      have h2 : B (L w) w = (starRingEnd ℂ) μ * B w w := by rw [hLsymm w hw w hw, hμ, hBsmul' μ w hw w hw]
      have h3 : (μ - (starRingEnd ℂ) μ) * B w w = 0 := by rw [sub_mul, ← h1, ← h2, sub_self]
      have hB0' : B w w ≠ 0 := by
        intro h; rw [h, Complex.zero_re] at hp; exact lt_irrefl _ hp
      have h4 : μ = (starRingEnd ℂ) μ := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hB0')
      exact (Complex.conj_eq_iff_re.1 h4.symm).symm
    refine ⟨hreal, ?_, ?_⟩
    ·
      have hXw := hXpF w hw
      have h1 : B (Xp w) (Xp w) = -((starRingEnd ℂ) (μ * μ + μ - 2) * B w w) := by
        rw [hadjp w hw _ hXw, hXmXp w hw]
        have hLLw : L (L w) = (μ * μ) • w := by rw [hμ, map_smul, hμ, smul_smul]
        rw [hLLw, hμ, show (μ * μ) • w + μ • w - (2 : ℂ) • w = (μ * μ + μ - 2) • w from by module,
          hBsmul' _ w hw w hw]
      have h2 := hBre_nonneg _ hXw
      rw [h1, hreal] at h2
      simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, map_ofNat, Complex.neg_re, Complex.mul_re,
        Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
        Complex.mul_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add] at h2
      rw [hBself w hw] at h2
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h2
      have h2' : 0 ≤ -((μ.re * μ.re + μ.re - 2) * (B w w).re) := by simpa using h2
      nlinarith [h2', hp]
    · have hXw := hXmF w hw
      have h1 : B (Xm w) (Xm w) = -((starRingEnd ℂ) (μ * μ - μ - 2) * B w w) := by
        rw [hadjm w hw _ hXw, hXpXm w hw]
        have hLLw : L (L w) = (μ * μ) • w := by rw [hμ, map_smul, hμ, smul_smul]
        rw [hLLw, hμ, show (μ * μ) • w - μ • w - (2 : ℂ) • w = (μ * μ - μ - 2) • w from by module,
          hBsmul' _ w hw w hw]
      have h2 := hBre_nonneg _ hXw
      rw [h1, hreal] at h2
      simp only [map_sub, map_mul, Complex.conj_ofReal, map_ofNat, Complex.neg_re, Complex.mul_re,
        Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
        Complex.mul_im, mul_zero, zero_mul, sub_zero, zero_add] at h2
      rw [hBself w hw] at h2
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h2
      have h2' : 0 ≤ -((μ.re * μ.re - μ.re - 2) * (B w w).re) := by simpa using h2
      nlinarith [h2', hp]

  have hspec : ∀ w ∈ F, w ≠ 0 → ∀ μ : ℂ, L w = μ • w → μ * (μ * μ - 1) = 0 := by
    intro w hw hw0 μ hμ
    obtain ⟨hreal, hb1, hb2⟩ := hbound w hw hw0 μ hμ
    set r : ℝ := μ.re with hr

    have hup : L (Xp w) = (μ + 1) • Xp w := by
      have h := hLXp w hw
      rw [sub_eq_iff_eq_add] at h
      rw [h, hμ, map_smul, add_smul, one_smul, add_comm]
    have hr_le : r ≤ 0 ∨ r = 1 := by
      by_cases hX : Xp w = 0
      ·
        have h0 : (μ * μ + μ - 2) • w = 0 := by
          have h := hXmXp w hw
          rw [hX, map_zero] at h
          have hLLw : L (L w) = (μ * μ) • w := by rw [hμ, map_smul, hμ, smul_smul]
          rw [hLLw, hμ] at h
          rw [show (μ * μ + μ - 2) • w = (μ * μ) • w + μ • w - (2 : ℂ) • w from by module]
          exact h.symm
        have hsc : μ * μ + μ - 2 = 0 := (smul_eq_zero.1 h0).resolve_right hw0
        rw [hreal] at hsc
        have : r * r + r - 2 = 0 := by exact_mod_cast hsc
        right; nlinarith [this, hb2]
      · obtain ⟨-, hb1', -⟩ := hbound _ (hXpF w hw) hX (μ + 1) hup
        left
        have : (μ + 1).re = r + 1 := by rw [Complex.add_re, Complex.one_re]
        rw [this] at hb1'
        nlinarith [hb1', hb1]

    have hdown : L (Xm w) = (μ - 1) • Xm w := by
      have h := hLXm w hw
      rw [sub_eq_iff_eq_add] at h
      rw [h, hμ, map_smul, sub_smul, one_smul]; abel
    have hr_ge : 0 ≤ r ∨ r = -1 := by
      by_cases hX : Xm w = 0
      · have h0 : (μ * μ - μ - 2) • w = 0 := by
          have h := hXpXm w hw
          rw [hX, map_zero] at h
          have hLLw : L (L w) = (μ * μ) • w := by rw [hμ, map_smul, hμ, smul_smul]
          rw [hLLw, hμ] at h
          rw [show (μ * μ - μ - 2) • w = (μ * μ) • w - μ • w - (2 : ℂ) • w from by module]
          exact h.symm
        have hsc : μ * μ - μ - 2 = 0 := (smul_eq_zero.1 h0).resolve_right hw0
        rw [hreal] at hsc
        have : r * r - r - 2 = 0 := by exact_mod_cast hsc
        right; nlinarith [this, hb1]
      · obtain ⟨-, -, hb2'⟩ := hbound _ (hXmF w hw) hX (μ - 1) hdown
        left
        have : (μ - 1).re = r - 1 := by rw [Complex.sub_re, Complex.one_re]
        rw [this] at hb2'
        nlinarith [hb2', hb2]
    have hr3 : r * (r * r - 1) = 0 := by
      rcases hr_le with h1 | h1 <;> rcases hr_ge with h2 | h2
      · have : r = 0 := le_antisymm h1 h2
        rw [this]; ring
      · rw [h2]; ring
      · rw [h1]; ring
      · rw [h1]; ring
    rw [hreal]; exact_mod_cast hr3

  intro f hf
  obtain ⟨s, g, hg, hfsum⟩ := exists_eigen_decomposition (Module.finrank ℂ F) F rfl B hlin hsymm hpos L hLF hLsymm f hf

  have hL3 : L (L (L f)) = L f := by
    rw [hfsum]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    obtain ⟨hgF, hgeig⟩ := hg μ hμ
    by_cases h0 : g μ = 0
    · simp [h0]
    · have hsp := hspec (g μ) hgF h0 μ hgeig
      rw [hgeig, map_smul, hgeig, map_smul, map_smul, hgeig, smul_smul, smul_smul]
      have : μ * μ * μ = μ := by linear_combination hsp
      rw [this]

  have h1 : J₃ (J₃ (J₃ f)) = Complex.I • L (L (L f)) := by
    rw [hJ3L (J₃ (J₃ f)), hJ3L (J₃ f), hJ3L f, map_smul, map_smul, map_smul, smul_smul, smul_smul]
    congr 1
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-Complex.I) * hI
  rw [h1, hL3, hJ3L f, neg_smul, neg_neg]

end SO3
end
end KSpec
end P2MW.S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition
