public section

open MeasureTheory Filter

open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  [NormedAddCommGroup E]

variable [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem integral_ae_eq_integral_jointRep [SigmaFinite μ] {ν : Measure β} [SFinite ν]
    (γ : β → Lp E 2 μ) (hγ : Integrable γ ν) (Γ : α × β → E)
    (hΓ : StronglyMeasurable Γ) (hrep : ∀ᵐ s ∂ν, (fun x => Γ (x, s)) =ᵐ[μ] γ s) :
    ((∫ s, γ s ∂ν : Lp E 2 μ) : α → E) =ᵐ[μ] fun x => ∫ s, Γ (x, s) ∂ν := by
  let I : Lp E 2 μ := ∫ s, γ s ∂ν
  let H : α → E := fun x => ∫ s, Γ (x, s) ∂ν
  have hHint : ∀ B : Set α, μ B < ⊤ → IntegrableOn H B μ := fun B hμB =>
    (integrable_jointRep_restrict_prod γ hγ Γ hΓ hrep hμB).integral_prod_left
  have hIint : ∀ B : Set α, μ B < ⊤ → IntegrableOn (I : α → E) B μ := fun B hμB => by
    have : IsFiniteMeasure (μ.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hμB⟩
    exact ((Lp.memLp I).restrict B).integrable (by norm_num)
  have hkey : ∀ (c : E) (B : Set α), MeasurableSet B → μ B < ⊤ →
      ∫ x in B, inner ℂ c ((I : α → E) x) ∂μ = ∫ x in B, inner ℂ c (H x) ∂μ := by
    intro c B hB hμB
    have hprod := integrable_jointRep_restrict_prod γ hγ Γ hΓ hrep hμB
    rw [← L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ I hB c hμB.ne]
    rw [← integral_inner hγ]
    have hstep : ∀ᵐ s ∂ν, inner ℂ (indicatorConstLp 2 hB hμB.ne c) (γ s) =
        ∫ x in B, inner ℂ c (Γ (x, s)) ∂μ := by
      filter_upwards [hrep] with s hs
      rw [L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ (γ s) hB c hμB.ne]
      exact integral_congr_ae (ae_restrict_of_ae (by
        filter_upwards [hs] with x hx
        exact congrArg (inner ℂ c) hx.symm))
    rw [integral_congr_ae hstep]
    have hswap := integral_integral_swap (μ := μ.restrict B) (ν := ν)
      (f := fun x s => inner ℂ c (Γ (x, s))) (hprod.const_inner c)
    rw [← hswap]
    apply integral_congr_ae
    filter_upwards [hprod.prod_right_ae] with x hx
    exact integral_inner hx c
  have hzero : ∀ c : E, (fun x => inner ℂ c ((I : α → E) x - H x)) =ᵐ[μ] 0 := by
    intro c
    refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun B _ hμB => ?_)
      (fun B hB hμB => ?_)
    · simp_rw [inner_sub_right]
      exact ((hIint B hμB).const_inner c).sub ((hHint B hμB).const_inner c)
    · simp_rw [inner_sub_right]
      rw [integral_sub ((hIint B hμB).const_inner c) ((hHint B hμB).const_inner c),
        hkey c B hB hμB, sub_self]
  let b := stdOrthonormalBasis ℂ E
  have hall : ∀ᵐ x ∂μ, ∀ i, inner ℂ (b i) ((I : α → E) x - H x) = 0 := by
    rw [ae_all_iff]
    intro i
    exact hzero (b i)
  filter_upwards [hall] with x hx
  have hsum := b.sum_repr' ((I : α → E) x - H x)
  simp only [hx, zero_smul, Finset.sum_const_zero] at hsum
  exact sub_eq_zero.1 hsum.symm

end CKN.Leray
end
end
