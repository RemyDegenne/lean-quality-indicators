namespace OAI

namespace Ostmann

open Complex Filter Set

open scoped Topology Classical

theorem PrimitiveComplexCharacter.completed_logDeriv_eq_add
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 ≤ s.re) :
    logDeriv χ.completed s = logDeriv χ.L s +
      logDeriv (DirichletCharacter.gammaFactor χ.character) s := by
  have hspos : 0 < s.re := by linarith
  have hne : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    have hh := χ.gammaInverse_ne_zero s hspos
    intro hz
    apply hh
    simp [PrimitiveComplexCharacter.gammaInverse, hz]
  have he : χ.completed =ᶠ[𝓝 s] (fun z => χ.L z * DirichletCharacter.gammaFactor χ.character z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hspos] with z hz
    exact χ.completed_eq_L_mul_gamma z hz
  rw [(logDeriv_congr_nhds he).self_of_nhds]
  exact logDeriv_fun_mul s (χ.L_ne_zero_one_le_re s hs) hne
    (χ.L_analytic s).differentiableAt (χ.gammaFactor_differentiableAt_pos s hspos)

end Ostmann
end OAI
