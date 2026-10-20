namespace P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two

attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

p2m_open_scoped

p2m_open

section IntModuleTransport

p2m_open

p2m_reactivate

section AnyIntAlgebra

attribute [-instance] AddCommGroup.toIntModule LieRing.instLieAlgebra

p2m_open_scoped "Module Module.Finite" in

p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt" in open _root_.P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep in

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

p2m_reactivate

p2m_reactivate

p2m_open

p2m_reactivate

p2m_reactivate

section Descent

variable {R : Type*} [CommRing R] (F : Type*) [CommRing F] [Algebra R F] (S : Submonoid R) [IsLocalization S F]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

p2m_reactivate

section PointsBaseChange

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
  (K : Type*) [Semiring K] [Bialgebra R K]
  (Ω : Type*) [CommSemiring Ω] [Algebra S Ω] [Algebra R Ω] [IsScalarTower R S Ω]

p2m_reactivate

p2m_open

section GroupLikeBaseChange

variable {R : Type*} [CommRing R] (F : Type*) [CommRing F] [Algebra R F]
  {B : Type*} [CommRing B] [Bialgebra R B]

p2m_reactivate

section Embedding

variable {R : Type*} [CommRing R] (S : Submonoid R) (F : Type*) [CommRing F] [Algebra R F] [IsLocalization S F]

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

section GroupLikeEval

variable {R : Type*} [CommSemiring R] {C : Type*} [Semiring C] [Bialgebra R C] {A : Type*} [CommSemiring A] [Algebra R A]

p2m_reactivate

p2m_reactivate

p2m_open

section IsCocommTransfer

variable {R : Type*} [CommSemiring R] {A B : Type*} [AddCommMonoid A] [Module R A] [Coalgebra R A]
  [AddCommMonoid B] [Module R B] [Coalgebra R B]

p2m_reactivate

p2m_reactivate

section FreeRank

variable (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

p2m_reactivate

p2m_reactivate

p2m_open

p2m_reactivate

section GroupLikeMonoidAlgebra

variable (F : Type*) [Field F] (Γ : Type*)

p2m_reactivate

p2m_reactivate

attribute [-instance] AddCommGroup.toIntModule LieRing.instLieAlgebra

p2m_reactivate

attribute [-instance] AddCommGroup.toIntModule LieRing.instLieAlgebra

p2m_reactivate

attribute [-instance] AddCommGroup.toIntModule LieRing.instLieAlgebra

p2m_reactivate

attribute [-instance] AddCommGroup.toIntModule LieRing.instLieAlgebra

p2m_reactivate

attribute [-instance] AddCommGroup.toIntModule LieRing.instLieAlgebra

p2m_reactivate

attribute [-instance] AddCommGroup.toIntModule LieRing.instLieAlgebra

p2m_reactivate

attribute [-instance] AddCommGroup.toIntModule LieRing.instLieAlgebra

p2m_reactivate

p2m_reactivate

p2m_reactivate

section LATTICE_KIT

p2m_reactivate

section BRIDGE

p2m_open

p2m_reactivate

namespace Module p2m_export "Module" "Flat Injective equiv Finite.equiv finrank Free finite_iff_isArtinianRing mk ext' Finite.of_injective free_of_finite_type_torsion_free' Finite.iff_fg restrictScalars finrank_baseChange Flat.isSMulRegular_of_nonZeroDivisors jacobson IsPrincipal Finite.of_exists_smul_isIntegral_maximal Finite.of_finite_baseChange_localization_maximal Finite.of_finite_algHom_of_isAlgClosed Finite.rat_baseChange_of_finite_algHom" namespace Flat p2m_export "Module.Flat" "out toAlgebra self trans baseChange isSMulRegular_of_nonZeroDivisors mk" end Module.Flat

namespace HopfAlgebra

namespace LocEt

p2m_open

p2m_open

p2m_reactivate

section StandardOrder

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (q : ℕ) [hq : Fact q.Prime]

local notation "Rℓ" => ratLocalizedAt ℓ

local notation "G" => Multiplicative (ZMod q)

local notation "V" => MonoidAlgebra ℚ (Multiplicative (ZMod q))

noncomputable def stdOrder : Subalgebra Rℓ V := (orderMap ℓ q).range

end StandardOrder
end LocEt
end HopfAlgebra
end Module
end BRIDGE
end LATTICE_KIT
end GroupLikeMonoidAlgebra
end FreeRank
end IsCocommTransfer
end GroupLikeEval
end Embedding
end GroupLikeBaseChange
end PointsBaseChange
end Descent
end AnyIntAlgebra
end IntModuleTransport
end P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two
