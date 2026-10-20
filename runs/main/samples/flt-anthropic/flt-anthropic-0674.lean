namespace P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed

attribute [-instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite

variable {𝔎 : Type} [Field 𝔎] {𝔏 : Type} [Field 𝔏] [Algebra 𝔎 𝔏] [IsAlgClosed 𝔏] [CharZero 𝔏]

local notation "Γℚ" => (𝔏 ≃ₐ[𝔎] 𝔏)

open scoped TensorProduct

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Ws25

namespace S3

open TensorProduct

p2m_reactivate

namespace DualPairing

variable {O : Type} [CommRing O] {H : Type} [CommRing H] [HopfAlgebra O H]

variable {L : Type} [Field L] [Algebra O L]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_sum_tmul_of_pairing (b : Module.Basis ι O H) (g : L ⊗[O] H) (f : CartierDual O H →ₐ[O] L)
    (hg : ∀ φ : CartierDual O H, TensorProduct.rid O L (LinearMap.lTensor L (CartierDual.toDual O H φ) g) = f φ) :
    g = ∑ k, f (db b k) ⊗ₜ[O] b k := by
  set B := Algebra.TensorProduct.basis L b with hB
  have hexp : g = ∑ k, (B.repr g k) ⊗ₜ[O] b k := by
    conv_lhs => rw [← B.sum_repr g]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hcoef : ∀ k, f (db b k) = B.repr g k := by
    intro k
    rw [← hg (db b k)]
    conv_lhs => rw [hexp]
    rw [map_sum, map_sum]
    simp_rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    have hdb : ∀ i, CartierDual.toDual O H (db b k) (b i) = if i = k then 1 else 0 := fun i => by
      rw [CartierDual.toDual_apply, db_apply_basis]
    simp_rw [hdb, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
  rw [hexp]
  exact Finset.sum_congr rfl fun k _ => by rw [hcoef k]

end DualPairing
end S3
end Ws25
end
end P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed
