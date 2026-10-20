namespace P2MW.S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd

set_option autoImplicit false

open scoped MatrixGroups ModularForm

open Matrix

namespace FALT

open ModularForm

variable {M q : ℕ}

open ModularForm

variable {M q : ℕ}

theorem val_mapGL' (γ : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

end FALT
end P2MW.S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd
