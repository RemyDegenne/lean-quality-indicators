@[expose] public section

noncomputable section

open MeasureTheory Homogenization

open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section4

/-- `d_m` source split with its first vector term left explicit.  The
first term is `(Jhat_m - J_m) Σ_l xihat_l (∇X_l∘X_l⁻¹)∇T`; the second is
the literal `A_{m,n,Jcut} q_{m,n,Jcut}` remainder. -/
def dmFrozenSource {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (first : ℝ × Vec 2 → Vec 2) (z : ℝ × Vec 2) : Vec 2 :=
  first z + ∑ n ∈ Finset.range (AVenhance.Nstar β),
    dmFrozenTailTerm I hΦ m κ T n z

end AVenhance.Infra.Section4
end
end
