namespace P2MW.S_LanglandsTunnell_CubicInduction_mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix Topology Filter

noncomputable section

namespace LanglandsTunnell

namespace CubicInduction

namespace JacquetVanishing

p2m_open

variable (v : HeightOneSpectrum (𝓞 ℚ))

variable {v}

variable (v)

scoped instance compactSpace_ball (k : ℤ) : CompactSpace (ball v k) :=
  isCompact_iff_compactSpace.mp (isCompact_ball v k)

scoped instance finite_quotient (c k : ℤ) : Finite (↥(ball v c) ⧸ (ball v k).addSubgroupOf (ball v c)) :=
  AddSubgroup.quotient_finite_of_isOpen _ (AddSubgroup.addSubgroupOf_isOpen _ _ (isOpen_ball v k))

scoped instance fintype_quotient (c k : ℤ) : Fintype (↥(ball v c) ⧸ (ball v k).addSubgroupOf (ball v c)) :=
  Fintype.ofFinite _

variable {v}

section PS

variable (v)

variable {v}

section Assembly

variable {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F : LocalGL3 v → ℂ} {θ : (v.adicCompletion ℚ)ˣ →* ℂˣ}
  {k c : ℤ}

theorem conj_lowerL_coe (x z α β : v.adicCompletion ℚ) :
    ((upperUnipotent3 (-x) 0 (-z) * lowerL α β * upperUnipotent3 x 0 z : LocalGL3 v) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1 - α * x - β * z, -(α * x * x) - β * x * z, -(α * x * z) - β * z * z;
         α, 1 + α * x, α * z;
         β, β * x, 1 + β * z] := by
  ext i j
  simp only [Units.val_mul, upperUnipotent3_coe, lowerL_coe]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

end Assembly
end PS
end JacquetVanishing
end CubicInduction
end LanglandsTunnell
end
end P2MW.S_LanglandsTunnell_CubicInduction_mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3
