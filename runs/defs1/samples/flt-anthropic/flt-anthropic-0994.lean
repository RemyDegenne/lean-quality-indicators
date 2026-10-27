namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant

set_option autoImplicit false

p2m_open

p2m_open

open scoped Topology ENNReal NNReal Matrix

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

p2m_reactivate

p2m_reactivate

p2m_open

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

p2m_open

p2m_reactivate

p2m_open

p2m_reactivate

p2m_reactivate

p2m_open

p2m_open

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

open Finset Polynomial

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

p2m_open

noncomputable section

namespace Ws1

namespace Middle

namespace Cells

variable (v : HeightOneSpectrum (𝓞 ℚ))

variable {v}

def dualCellIntegrand {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (V : LocalGL3 v → ℂ) (ℓ : ℕ) (χD : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (fD : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (w₀ : GL (Fin 2) (v.adicCompletion ℚ)) (s : ℂ)
    (y : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) : ℂ :=
  letI := localBorel ℚ v
  fD (w₀ * unipotentGL2 y) *
    (((χD 0 a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ ((1 - s) - 1) *
      localZeta31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (fun x : LocalGL3 v => dualWhittakerFn3 V (x * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (χD 1) (1 - s) (iotaGL (diagUnits2 1 a * unipotentGL2 y)))

end Cells
end Middle
end Ws1
end
end
end
end
end
end P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant
