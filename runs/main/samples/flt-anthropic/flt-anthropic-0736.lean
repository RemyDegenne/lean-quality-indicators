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

p2m_reactivate

p2m_reactivate

namespace DualFlag

open DualPairing DualChar

section Context

variable {O : Type} [CommRing O] [Algebra O (𝔏)] {HO : Type} [CommRing HO] [HopfAlgebra O HO]

variable [Module.Finite O HO] [Module.Free O HO]

variable {I : Subgroup (𝔏 ≃ₐ[𝔎] 𝔏)} {J : Type} [AddCommGroup J] [DistribMulAction ↥I J]

variable {M : AddSubgroup J} (pts : WithConv (HO →ₐ[O] 𝔏) ≃ ↥M)

variable (hadd : ∀ f g, pts (f * g) = pts f + pts g)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (gl : GLData O HO (𝔏)) (b : Module.Basis ι O HO)

omit [Module.Finite O HO] [Module.Free O HO] [DistribMulAction ↥I J] in
include hadd in
theorem pow_natCard_eq_one (f : WithConv (HO →ₐ[O] 𝔏)) : f ^ Nat.card ↥M = 1 := by
  apply pts.injective
  rw [pts_pow pts hadd, pts_one pts hadd, card_nsmul_eq_zero']

end Context
end DualFlag
end S3
end Ws25
end
end P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed
