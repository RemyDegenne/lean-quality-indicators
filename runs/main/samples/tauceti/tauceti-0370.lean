public section

open DirectSum PowerSeries

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (𝒞 : ℤ → Submodule R A) [GradedAlgebra 𝒞]

theorem iSupIndep_adamsCompletionGrading : iSupIndep (adamsCompletionGrading 𝒜 𝒞) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum p hp
  have h𝒞 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero 𝒞).1
    (DirectSum.Decomposition.isInternal 𝒞).submodule_iSupIndep
  apply Subtype.ext
  ext n
  rw [Subalgebra.coe_zero, map_zero]
  refine h𝒞 s (fun q => coeff n (v q : PowerSeries A))
    (fun q hq => ((mem_adamsCompletionGrading_iff 𝒜 𝒞).1 (hv q hq) n).2) ?_ p hp
  rw [← map_sum, ← AddSubmonoidClass.coe_finsetSum, hsum, Subalgebra.coe_zero, map_zero]

end TauCeti
end
