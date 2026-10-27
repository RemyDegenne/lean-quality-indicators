namespace P2MW.S_ModularCurve_eventually_norm_slash_le_mul_of_isIntegral_adjoin_jqModC_inv_sq

p2m_open

open scoped MatrixGroups ModularForm Manifold

set_option autoImplicit false

noncomputable section

namespace ANb

local notation "𝒩" => niceSubalgebra

def qexpHom : 𝒩 →ₐ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 (f : ℍ → ℂ)
  map_one' := UpperHalfPlane.qExpansion_one 1
  map_mul' f g := UpperHalfPlane.qExpansion_mul (an f) (an g)
  map_zero' := UpperHalfPlane.qExpansion_zero 1
  map_add' f g := UpperHalfPlane.qExpansion_add (an f) (an g)
  commutes' c := by
    have h1 : ((algebraMap ℂ (ℍ → ℂ) c : ℍ → ℂ)) = c • (1 : ℍ → ℂ) := by
      funext z; simp
    have a1 : AnalyticAt ℂ (cuspFunction 1 (1 : ℍ → ℂ)) 0 := an (1 : 𝒩)
    change qExpansion 1 (algebraMap ℂ (ℍ → ℂ) c) = _
    rw [h1, UpperHalfPlane.qExpansion_smul a1 c, UpperHalfPlane.qExpansion_one,
      Algebra.algebraMap_eq_smul_one]

end ANb
end
end P2MW.S_ModularCurve_eventually_norm_slash_le_mul_of_isIntegral_adjoin_jqModC_inv_sq
