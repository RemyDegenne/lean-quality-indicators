namespace P2MW.S_GaloisRepAdic_det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor

attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois

open Polynomial

noncomputable section

namespace DetFrob

set_option linter.unusedSectionVars false

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

local notation "ℚbar" => AlgebraicClosure ℚ

section Diag

variable {O : Type} [CommRing O] [IsLocalRing O]

def diagAdic (χ : Gal →* Oˣ) (hχ : CharCont χ) : GaloisRepAdic O where
  V := Fin 2 → O
  finrank_eq := Module.finrank_fin_fun O
  ρ := diagHom χ
  isAdicContinuous := by
    intro n
    obtain ⟨L, hL, h⟩ := hχ n
    refine ⟨L, hL, fun σ hσ v => ?_⟩
    apply mem_smul_top_of_forall
    intro i
    rw [Pi.sub_apply, diagHom_apply, diagEnd_apply]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← sub_one_mul]
      exact Ideal.mul_mem_right _ _ (h σ hσ)
    · simp

end Diag
end DetFrob
end
end P2MW.S_GaloisRepAdic_det_eq_mul_of_isFrobeniusAt_of_det_frobenius_eq_mul_of_not_dvd_conductor
