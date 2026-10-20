namespace P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass

set_option autoImplicit false

set_option Elab.async false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_FujisakiC2c

set_option autoImplicit false

p2m_open

open IsDedekindDomain FractionalIdeal M4aHerbrand MeasureTheory Topology M4aLocalCFT

open scoped NNReal nonZeroDivisors

noncomputable section

namespace M4aLocalCFT

namespace FujisakiC2c

variable {F : Type} [Field F] [NumberField F]

theorem exists_mul_principal_inv_mem_unitsOutside {x : (AdeleRing (𝓞 F) F)ˣ} (hx : ideleClass x = 1) :
    ∃ α : Fˣ, x * (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α)⁻¹
      ∈ unitsOutside (F := F) ∅ := by
  have hP : (((ideleIdeal x : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F).IsPrincipal := by
    have h := hx
    rw [ideleClass, MonoidHom.comp_apply, ClassGroup.mk_eq_one_iff] at h
    exact h
  obtain ⟨a, ha⟩ := (FractionalIdeal.isPrincipal_iff _).mp hP
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [spanSingleton_zero] at ha
    exact (ideleIdeal x).ne_zero ha
  refine ⟨Units.mk0 a ha0, ?_⟩
  rw [← ker_ideleIdeal, MonoidHom.mem_ker, map_mul, map_inv, ideleIdeal_principal, mul_inv_eq_one]
  ext : 1
  rw [ha, coe_toPrincipalIdeal, Units.val_mk0]

end FujisakiC2c
end M4aLocalCFT
end
end Fold_FujisakiC2c
end P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass
