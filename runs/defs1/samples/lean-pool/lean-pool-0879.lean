@[expose] public section

open scoped BigOperators nonZeroDivisors Polynomial

open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) canonicalDifferentPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance canonicalDifferentPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def]
    rw [map_mul]
    change (algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) *
      algebraMap (RatFunc K) L s) * x =
      algebraMap K[X] L r * (algebraMap (RatFunc K) L s * x)
    rw [show algebraMap K[X] L r =
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) by rfl]
    ring⟩

local instance canonicalDifferentFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance canonicalDifferentFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance canonicalDifferentPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance canonicalDifferentFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance canonicalDifferentFiniteBaseFaithfulSmulFractionRing :
    FaithfulSMul K[X]
      (FractionRing (RatFuncFiniteIntegralClosure K L)) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  have hS := IsFractionRing.injective (RatFuncFiniteIntegralClosure K L)
    (FractionRing (RatFuncFiniteIntegralClosure K L)) hxy
  exact FunctionField.ringOfIntegers.algebraMap_injective K L hS

local instance canonicalDifferentFiniteFractionRingAlgebra :
    Algebra (FractionRing K[X])
      (FractionRing (RatFuncFiniteIntegralClosure K L)) :=
  FractionRing.liftAlgebra K[X]
    (FractionRing (RatFuncFiniteIntegralClosure K L))

local instance canonicalDifferentFiniteFractionRingSeparable :
    Algebra.IsSeparable (FractionRing K[X])
      (FractionRing (RatFuncFiniteIntegralClosure K L)) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (ratFuncFiniteFractionRingEquiv K).symm.toRingEquiv
    (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm.toRingEquiv ?_
  ext z
  exact IsFractionRing.algEquiv_commutes
    (ratFuncFiniteFractionRingEquiv K).symm
    (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm z

local instance canonicalDifferentInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance canonicalDifferentInfinityIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance canonicalDifferentInfinityTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance canonicalDifferentInfinityIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance canonicalDifferentInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance canonicalDifferentInfinityIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance canonicalDifferentInfinityPlaceFintype :
    Fintype (FiniteExtensionInfinityPlace K L) :=
  Set.Finite.fintype
    (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace K).asIdeal
      (RatFuncInfinityIntegralClosure K L))

/-- Residue- and base-place-degree weighted finite different degree. -/
def finiteExtensionFiniteDifferentDegree
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥) : ℕ :=
  (differentMultiplicityDivisor K[X]
      (RatFuncFiniteIntegralClosure K L) hDifferent).sum
    (fun q e => e * q.asIdeal.inertiaDeg K[X] *
      ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q))

end
end BGS.CorvajaZannier
end
