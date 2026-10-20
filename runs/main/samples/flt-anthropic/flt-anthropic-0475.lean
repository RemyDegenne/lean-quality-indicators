namespace P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent

set_option autoImplicit false

open UpperHalfPlane

open scoped MatrixGroups

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace RedRankCusp

section Main

variable {N : ℕ} {k : ℤ}

local notation "Γ₀(" N ")" => Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)

local notation "MF" => CuspForm Γ₀(N) k

variable (N k)

theorem modPCusp_finite [NeZero N] (F : Type) [Field F] : Module.Finite F ↥(ModPForms.modPCusp N k F) := by
  classical
  haveI : FiniteDimensional ℂ MF := finiteDimensional_cuspForm N k
  obtain ⟨hfin, hfree⟩ := latt_finite_free (N := N) (k := k) (⊤ : Submodule ℂ MF)
  haveI := hfin; haveI := hfree
  let b := Module.Free.chooseBasis ℤ (latt (⊤ : Submodule ℂ MF))
  let S : Submodule F (PowerSeries F) := Submodule.span F (Set.range fun j => red F (b j))
  haveI : FiniteDimensional F S := FiniteDimensional.span_of_finite F (Set.finite_range _)
  have hle : ModPForms.modPCusp N k F ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro φ ⟨g, a, hga, rfl⟩
    let v : latt (⊤ : Submodule ℂ MF) := ⟨g, Submodule.mem_top, fun n => ⟨a n, hga n⟩⟩
    have : (PowerSeries.mk fun n => ((a n : ℤ) : F)) = red F v := by
      ext n
      rw [PowerSeries.coeff_mk, coeff_red, ic_eq_of_qCoeff_eq v n (a n) (hga n)]
    rw [this]
    exact red_mem_span F b v
  exact Submodule.finiteDimensional_of_le hle

end Main
end RedRankCusp
end P2MW.S_ModPForms_card_le_finrank_modPCusp_of_linearIndependent
