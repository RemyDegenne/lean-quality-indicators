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

variable [Finite ↥M] (hMstab : ∀ (σ : ↥I) (x : J), x ∈ M → σ • x ∈ M)

variable [Coalgebra.IsCocomm O HO]

theorem pts₂_val [Nontrivial O] (hcard : Nat.card ↥M = Module.finrank O HO)
    (f : WithConv (CartierDual O HO →ₐ[O] 𝔏)) :
    ((pts₂ pts hadd gl b hMstab hcard f : ↥(M₂ pts hadd gl b hMstab)) : Car ↥M (rhoM M hMstab)) =
      chi pts hadd gl b hMstab (WithConv.ofConv f) := rfl

end Context
end DualFlag
end S3
end Ws25
end
end P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed
