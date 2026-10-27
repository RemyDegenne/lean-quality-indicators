namespace P2MW.S_ModularCurve_exists_descent_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open scoped TensorProduct

open scoped TensorProduct

open scoped TensorProduct

namespace QB

open PDivisibleGroup

variable {Rh : Type} [CommRing Rh] [IsDomain Rh] [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
  {p : ℕ} [Fact p.Prime] {h hB : ℕ} (𝒢 : PDivisibleGroup Rh p h) (ℬ : PDivisibleGroup Rh p hB) (v : ℕ)
  (ψ : ℬ.level v →ₐc[Rh] 𝒢.level v)

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable def sPt (w : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.Point ℚ̄ v →* 𝒢.Point ℚ̄ v := Hopf.convCompMonoidHom ℚ̄ w

end QB
end P2MW.S_ModularCurve_exists_descent_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness
