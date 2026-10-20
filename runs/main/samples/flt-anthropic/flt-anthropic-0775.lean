namespace P2MW.S_PDivisibleGroup_free_cotangent_of_isArtinianRing_of_pow_eq_zero

attribute [-instance] PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra

attribute [-instance] HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open scoped TensorProduct

open Coalgebra Bialgebra IsLocalRing Function

namespace PDivFreeCot

section Final

variable {R : Type} [CommRing R] [IsArtinianRing R] [IsLocalRing R] {p h : ℕ} [Fact p.Prime]
  (G : PDivisibleGroup R p h) (hp : (p : R) ∈ maximalIdeal R) [CharP (kk R) p]

include hp in
theorem iInf_ker_phi : (⨅ d, RingHom.ker (phi G hp d)) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_iInf] at hf
  exact (Submodule.mem_bot _).2 (eq_zero_of_forall_phi G hp f fun d => hf d)

end Final
end PDivFreeCot
end
end P2MW.S_PDivisibleGroup_free_cotangent_of_isArtinianRing_of_pow_eq_zero
