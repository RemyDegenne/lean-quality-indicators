namespace OAI

section

section

open scoped symmDiff

namespace SimpleAmenable

open scoped commutatorElement

open scoped commutatorElement

section AffineDensityEnergy

open Classical Matrix MeasureTheory

open scoped Matrix.Norms.Elementwise

theorem affineNoiseRoot_derivative_energy {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hn : (∫x : ℝ,f x^2)=1) (he : Function.Even f)
    {A : ℝ → Matrix ι ι ℝ} {a : ℝ → ι → ℝ}
    {A' : Matrix ι ι ℝ} {a' : ι → ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (ha : HasDerivAt a a' t)
    (hpos : 0<(A t).det) :
    (∫y : ι → ℝ,deriv (fun s => affineNoiseRoot f (A s) (a s) y) t^2)≤
      affineNoiseEnergyConstant f*((∑i,∑j,((A t)⁻¹*A') i j^2)+
        ∑i,((A t)⁻¹*ᵥa') i^2) := by
  have hd (y : ι → ℝ) := (affineNoiseRoot_hasDerivAt (hf.differentiable (by norm_num))
    hA ha hpos y).deriv
  simp_rw [hd,div_pow,neg_sq,Real.sq_sqrt hpos.le]
  rw [integral_div,integral_matrix_affine_inverse (A t) (a t)
    (isUnit_iff_ne_zero.mpr hpos.ne')
    (fun x => affineNoiseGenerator f ((A t)⁻¹*A') ((A t)⁻¹*ᵥa') x^2),
    abs_of_pos hpos,mul_div_cancel_left₀ _ hpos.ne']
  exact affineNoiseGenerator_energy hf hc he hn _ _

end AffineDensityEnergy
end SimpleAmenable
end
end
end OAI
