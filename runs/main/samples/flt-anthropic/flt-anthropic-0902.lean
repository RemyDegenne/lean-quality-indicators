namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace U2Dual

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)

local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

local notation "K0" => (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ)))

local notation "ψp" => (NumberField.StandardAddChar.psiLocal ℚ p)

scoped instance charZero_Fp : CharZero (p.adicCompletion ℚ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (p.adicCompletion ℚ)).injective

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem norm_le_one_iff_mem (x : F) : ‖x‖ ≤ 1 ↔ x ∈ (O) := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← (Valued.v : Valuation F _).map_one, ← norm_le_norm_iff_v_le_v p,
    norm_one]

end U2Dual
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2
