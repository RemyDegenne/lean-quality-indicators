namespace P2MW.S_CerednikDrinfeld_germ_app_decomposition_eq_of_germ_eq_of_iso_pullback_completion_zero_one_of_two_mul_dvd

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

set_option linter.unusedVariables false

set_option maxHeartbeats 160000000

set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField MatrixGroups

open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega

open scoped Classical

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra

theorem rdg_isIso_pullback_twist {X B S : Scheme.{0}} (f : X ⟶ S) (b : B ⟶ S) (e e' : B ⟶ B)
    (he : e ≫ b = b) (he' : e' ≫ b = b) (h1 : e ≫ e' = 𝟙 _) (h2 : e' ≫ e = 𝟙 _) :
    IsIso (Limits.pullback.lift (Limits.pullback.fst f b) (Limits.pullback.snd f b ≫ e)
      (by rw [Category.assoc, he]; exact Limits.pullback.condition)) := by
  refine ⟨⟨Limits.pullback.lift (Limits.pullback.fst f b) (Limits.pullback.snd f b ≫ e')
      (by rw [Category.assoc, he']; exact Limits.pullback.condition), ?_, ?_⟩⟩
  · apply Limits.pullback.hom_ext
    · simp only [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, Limits.pullback.lift_snd, Category.id_comp]
      rw [Limits.pullback.lift_snd_assoc, Category.assoc, h1, Category.comp_id]
  · apply Limits.pullback.hom_ext
    · simp only [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, Limits.pullback.lift_snd, Category.id_comp]
      rw [Limits.pullback.lift_snd_assoc, Category.assoc, h2, Category.comp_id]

end P2MW.S_CerednikDrinfeld_germ_app_decomposition_eq_of_germ_eq_of_iso_pullback_completion_zero_one_of_two_mul_dvd
