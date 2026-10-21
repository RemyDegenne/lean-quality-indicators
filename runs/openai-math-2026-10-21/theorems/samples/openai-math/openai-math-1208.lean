namespace OAI

section

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section

open scoped BigOperators Classical

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

open UniqueGamesTheorem.Inverse.KMSBasisInvariant

universe u v w x

variable {E : Type u} {F : Type v} {I : Type w} {J : Type x}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 I] [FiniteDimensional F2 J]
  [Finite E] [Finite F] [Finite I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (KMSKernelFiberCard.KernelClass F I)]

omit [Finite F] in
theorem smallComponent_energy_base_bound (ι : I →ₗ[F2] E)
    (hι : Function.Injective ι) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (ε : ℝ)
    (hg : HomogeneousRestrictionBound (Module.finrank F2 I) ε f) :
    (2 : ℝ) ^ (Module.finrank F2 I * Module.finrank F2 E) *
        (𝔼 X, smallComponent ι f X ^ 2) ≤
      (2 : ℝ) ^ (4 * Module.finrank F2 I * Module.finrank F2 I) * ε := by
  have hdim : Module.finrank F2 I ≤ Module.finrank F2 E :=
    LinearMap.finrank_le_finrank_of_injective hι
  have henergy : (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) ≤ ε :=
    (component_energy_le (fun T : F →ₗ[F2] E =>
      Module.finrank F2 T.range = Module.finrank F2 I) f).trans (hg.energy_le _ _ _)
  have hε : 0 ≤ ε := (Finset.expect_nonneg (fun _ _ => sq_nonneg _)).trans henergy
  have hbase := KMSInjectionCount.pow_mul_le_of_beta_cross_mul I E hdim
    (Finset.expect_nonneg (fun _ _ => sq_nonneg (smallComponent ι f _)))
    (Finset.expect_nonneg (fun _ _ => sq_nonneg (rankComponent (Module.finrank F2 I) f _)))
    (smallComponent_energy_cross_mul ι hι f hf)
  calc
    _ ≤ (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) *
        (𝔼 X, rankComponent (Module.finrank F2 I) f X ^ 2) := hbase
    _ ≤ (2 : ℝ) ^ (2 * (Module.finrank F2 I * Module.finrank F2 I)) * ε :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by nlinarith)) hε

end
end UniqueGamesTheorem.Inverse.KMSAnalytic
end
end OAI
