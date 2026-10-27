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

namespace Ws1

namespace Middle

namespace TorusUnique

open MvPolynomial

def LRep (f : ℂ → ℂ → ℂ) : Prop :=
  ∃ (M : MvPolynomial (Fin 2) ℂ) (A B : ℕ),
    ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → f x y * x ^ A * y ^ B = MvPolynomial.eval ![x, y] M

end TorusUnique
end Middle
end Ws1
end
end P2MW.S_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant
