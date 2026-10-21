namespace OAI

section

noncomputable section

open scoped RealInnerProductSpace ContDiff

namespace TamingCompatibility.Concentration

open PlaneVariation UnitaryFrame

lemma sqrt_angular_transverse {χ k δ t : ℝ} (hχ : 0 ≤ χ) (hk : 0 ≤ k)
    (hδ : 0 ≤ δ) (ht : 0 ≤ t) :
    Real.sqrt (χ*δ^2*k)*Real.sqrt (χ*k*t^2) = χ*k*δ*t := by
  rw [←Real.sqrt_mul (by positivity)]
  have he : χ*δ^2*k*(χ*k*t^2) = (χ*k*δ*t)^2 := by ring
  rw [he,Real.sqrt_sq (by positivity)]

end TamingCompatibility.Concentration
end
end
end OAI
