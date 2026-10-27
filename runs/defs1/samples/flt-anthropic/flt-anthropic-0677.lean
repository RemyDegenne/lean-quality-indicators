namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_conjBlockHarmonicOne_colHarmonic_gaussian3

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction MeasureTheory

namespace Ws23PhiFlat

open LanglandsTunnell.Converse.ArchR Set

section Pointwise

variable (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
  (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
  {P : RealArchParam} (D : ArchDatumR P) (n : ℕ)
  (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ ((n + 1 : ℕ) : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
  (u₃ : ℂ) (a₃ : ZMod 2) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
  (hS : S = fun M =>
      ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) *
      ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
  (c : ℝ) (hc : c ≠ 0)

noncomputable def Gfun (e : Fin 2 → Fin 2 → ℝ) : ℂ :=
  godementInner3 psiInf S (Matrix.of e) 1 *
    quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
    D.W (diagOne c * (Matrix.of e)⁻¹)

end Pointwise
end Ws23PhiFlat
end P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_conjBlockHarmonicOne_colHarmonic_gaussian3
