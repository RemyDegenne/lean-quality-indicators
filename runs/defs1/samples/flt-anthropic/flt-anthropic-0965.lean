namespace P2MW.S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

open IsLocalRing CuspForm.TWLevel

noncomputable section

namespace TWFreeSol

open CongruenceSubgroup

open scoped MatrixGroups IsMulCommutative

attribute [-instance] SetLike.GradeZero.instSemiring SetLike.GradeZero.instCommSemiring
  SetLike.GradeZero.instRing SetLike.GradeZero.instCommRing SetLike.GradeZero.instAlgebra

scoped instance (priority := high) commRingOpSubalgebra {R : Type} [CommRing R] {W : Type} [AddCommGroup W]
    [Module R W] {k : Type} [Field k] [Algebra R k] (D : CohCarrier.HeckeData R W k) :
    CommRing ↥D.opSubalgebra :=
  IsMulCommutative.instCommRing

section Bridge

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (p : ℕ) (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
  {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hqp : ∀ i, (qv i).Prime)
  (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
  (α : Fin t → ResidueField 𝒪)
  (H : Subgroup (ZMod (level N r qv))ˣ) (hc : OpComm N r qv S 𝒪 H)
  (hcG : CommG S N r qv hqp H (𝒪 := 𝒪))

local notation3 "VV" => CohCarrier.H1 (level N r qv) H 𝒪

local notation3 "DT" => heckeData N r qv S 𝒪 H θ α hc

local notation3 "FF" => (heckeData N r qv S 𝒪 H θ α hc).FreeAlg

local notation3 "𝔪" => (heckeData N r qv S 𝒪 H θ α hc).mTheta

local notation3 "𝕋" => (DG S N r qv hqp θ α H hcG).opSubalgebra

variable (hpow : ∃ n : ℕ, ∀ u ∈ HR N r qv, u ^ p ^ n ∈ H)

variable (Sp : IharaLemma.IdempotentSplitting
    ↥(DG S N r qv hqp θ α H hcG).opSubalgebra) (i₀ : Fin Sp.n)
  (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
  (hπk : ∀ g : Gen (level N r qv) S t,
    πk (Sp.toCornerRing i₀ (gG S N r qv hqp θ α H hcG (Sum.inl g))) =
      thetaQ N r qv S (ResidueField 𝒪) θ α g)

local notation3 "PP" =>
  ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 (level N r qv) H 𝒪) (Sp.e i₀))

attribute [local instance] modP

scoped instance towerP : IsScalarTower 𝒪 FF PP :=
  ⟨fun a f y => Subtype.ext (by
    change ((ψ S N r qv hqp θ α H hc hcG (a • f) : ↥𝕋) : Module.End 𝒪 VV) (y : VV) =
      a • ((ψ S N r qv hqp θ α H hc hcG f : ↥𝕋) : Module.End 𝒪 VV) (y : VV)
    rw [map_smul, Subalgebra.coe_smul, LinearMap.smul_apply])⟩

def fL : VV →ₗ[FF] PP where
  toFun := IharaLemma.toCorner (M := VV) (Sp.e i₀)
  map_add' v w := map_add _ v w
  map_smul' f v := by
    apply Subtype.ext
    rw [RingHom.id_apply, freeAlg_smul_P, Submodule.coe_smul, IharaLemma.toCorner_apply,
      IharaLemma.toCorner_apply, smul_eq_ψ_smul S N r qv hqp θ α H hc hcG, smul_smul, smul_smul,
      mul_comm]

end Bridge
end TWFreeSol
end
end P2MW.S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ
