namespace P2MW.S_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag

namespace FppfSubsheafFlagSol

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

open WithConv

section Algebra

variable {R : Type*} [CommRing R]

variable {H B A : Type*} [CommRing H] [HopfAlgebra R H] [CommRing B] [HopfAlgebra R B]
  [CommRing A] [Algebra R A]

lemma antipode_convMul (g : B →ₐ[R] A) :
    toConv (g.comp (antipodeAlgHom (R := R) B)) * toConv g = 1 := by
  refine WithConv.ext (AlgHom.ext fun c => ?_)
  change (toConv (g.comp (antipodeAlgHom (R := R) B)) * toConv g) c =
    (1 : WithConv (B →ₐ[R] A)) c
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  let ℛ := Coalgebra.Repr.arbitrary R c
  rw [← ℛ.eq, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
    Function.comp_apply, antipodeAlgHom_apply]
  rw [← g.commutes, ← HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit ℛ, map_sum]
  simp only [map_mul]

end Algebra
end FppfSubsheafFlagSol
end P2MW.S_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag
