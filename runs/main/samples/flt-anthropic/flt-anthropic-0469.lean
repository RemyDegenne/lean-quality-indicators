namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2

set_option autoImplicit false

open MeasureTheory

open scoped ENNReal NNReal Pointwise

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace HaarQuotient

namespace CellMajorantLoc

namespace LocalGL2Iwasawa

p2m_open

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem scalarPi_zpow_mul_diagZ_eq_shellRep (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)
    (hϖ : Valued.v ((ϖ : HeightOneSpectrum.adicCompletionIntegers K v) : HeightOneSpectrum.adicCompletion K v) =
      WithZero.exp (-1 : ℤ)) (dn : ℤ × ℤ) :
    scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion K v) ϖ) hπ ^ dn.2 *
        diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion K v) ϖ) hπ dn.1 =
      shellRep K v ϖ hϖ (dn.2 + dn.1, dn.2) := by
  rw [scalarPi_eq_diagU K v ϖ hπ hϖ, diagZ_eq_diagU K v ϖ hπ hϖ, diagU_zpow, diagU_mul, shellRep, zpow_add, mul_one]

end LocalGL2Iwasawa
end CellMajorantLoc
end HaarQuotient
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2
