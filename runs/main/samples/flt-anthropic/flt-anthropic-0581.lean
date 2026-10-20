namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_det_gen_mul_eq_nebentypus_mul

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

open NumberField.AdelicHaar

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open scoped ModularForm

noncomputable section

namespace Ws41

namespace Lift8

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix Rat.HeightOneSpectrum

open scoped MatrixGroups ModularForm

variable {M : ℕ}

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ

local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem finEmbed_glFin_of_glArch_eq_one' (u : AdelicGL2 (𝓞 ℚ) ℚ) (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ u) = u := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hmat : AdelicDock.finMat (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
    refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
    · rw [AdelicDock.mapMatrix_arch_finMat]
      ext i j
      have h : (glArch (𝓞 ℚ) ℚ u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j
          = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j := by rw [hu, Units.val_one]
      rw [glArch_apply] at h
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]
      exact h.symm
    · rw [AdelicDock.mapMatrix_fin_finMat]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, glFin_apply]
  rw [AdelicDock.coe_finEmbed, hmat]

end Lift8
end Ws41
end
end P2MW.S_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_det_gen_mul_eq_nebentypus_mul
