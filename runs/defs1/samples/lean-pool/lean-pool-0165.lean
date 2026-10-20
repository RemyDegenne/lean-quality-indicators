@[expose] public section

open scoped BigOperators nonZeroDivisors Pointwise Polynomial

open IsDedekindDomain

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]

variable (M : Type*) [Field M] [Algebra (RatFunc K) M]
  [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M]

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
  [Algebra M L] [IsScalarTower (RatFunc K) M L]

local instance (priority := 10) finitePlaceTowerPolynomialAlgebraM : Algebra K[X] M :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) M).comp
    (algebraMap K[X] (RatFunc K)))

local instance (priority := 10) finitePlaceTowerPolynomialAlgebraL : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance finitePlaceTowerPolynomialRatFuncM :
    IsScalarTower K[X] (RatFunc K) M :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finitePlaceTowerPolynomialRatFuncL :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finitePlaceTowerPolynomialFields : IsScalarTower K[X] M L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) x) =
      algebraMap M L
        (algebraMap (RatFunc K) M (algebraMap K[X] (RatFunc K) x))
    exact IsScalarTower.algebraMap_apply (RatFunc K) M L _

local instance finitePlaceTowerIntegralClosureAlgebra :
    Algebra (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  (finiteIntegralClosureMap K M L).toAlgebra

local instance finitePlaceTowerIntermediateIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K M) :=
  IsIntegralClosure.isIntegral_algebra K[X] M

local instance finitePlaceTowerIntermediateModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K M) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K M)

local instance finitePlaceTowerIntermediateTorsionFree :
    Module.IsTorsionFree K[X] M :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) M

local instance finitePlaceTowerIntermediateClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K M) :=
  IsIntegralClosure.isTorsionFree K[X] M

local instance finitePlaceTowerIntermediateDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K M) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) M
    (RatFuncFiniteIntegralClosure K M)

local instance finitePlaceTowerBaseIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance finitePlaceTowerTopModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance finitePlaceTowerTopTorsionFree :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance finitePlaceTowerTopClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance finitePlaceTowerTopDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance finitePlaceTowerIntegralClosures :
    IsScalarTower K[X] (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq fun _ => by
    apply Subtype.ext
    change algebraMap K[X] L _ = algebraMap M L (algebraMap K[X] M _)
    exact IsScalarTower.algebraMap_apply K[X] M L _

local instance finitePlaceTowerTopIntegral :
    Algebra.IsIntegral (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  Algebra.IsIntegral.tower_top K[X]

local instance finitePlaceTowerFaithful :
    FaithfulSMul (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply Subtype.ext
  apply (algebraMap M L).injective
  exact congrArg Subtype.val hxy

local instance finitePlaceTowerRelativeModuleFinite :
    Module.Finite (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
  Module.Finite.of_restrictScalars_finite K[X]
    (RatFuncFiniteIntegralClosure K M)
    (RatFuncFiniteIntegralClosure K L)

local instance finitePlaceTowerIntermediateFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K M) M :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    K[X] (RatFunc K) M (RatFuncFiniteIntegralClosure K M)

local instance finitePlaceTowerTopFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    K[X] (RatFunc K) L (RatFuncFiniteIntegralClosure K L)

local instance finitePlaceTowerIntermediateClosureFieldTower :
    IsScalarTower (RatFuncFiniteIntegralClosure K M) M L :=
  inferInstance

local instance finitePlaceTowerTopClosureFieldTower :
    IsScalarTower (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def, map_mul]
    rw [show algebraMap (RatFuncFiniteIntegralClosure K L) L
        (algebraMap (RatFuncFiniteIntegralClosure K M)
          (RatFuncFiniteIntegralClosure K L) r) =
        algebraMap (RatFuncFiniteIntegralClosure K M) L r by rfl]
    ring⟩

local instance finitePlaceTowerRelativeIsIntegralClosure :
    IsIntegralClosure (RatFuncFiniteIntegralClosure K L)
      (RatFuncFiniteIntegralClosure K M) L :=
  IsIntegralClosure.tower_top (R := K[X])

local instance infinityPlaceTowerIntegralClosureAlgebra :
    Algebra (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
  (infinityIntegralClosureMap K M L).toAlgebra

local instance infinityPlaceTowerIntermediateIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) M

local instance infinityPlaceTowerIntermediateModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) M
    (RatFuncInfinityIntegralClosure K M)

local instance infinityPlaceTowerIntermediateClosureTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) M

local instance infinityPlaceTowerIntermediateDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K)
    (RatFunc K) M (RatFuncInfinityIntegralClosure K M)

local instance infinityPlaceTowerBaseIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance infinityPlaceTowerTopModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityPlaceTowerTopClosureTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance infinityPlaceTowerTopDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K)
    (RatFunc K) L (RatFuncInfinityIntegralClosure K L)

local instance infinityPlaceTowerIntegralClosures :
    IsScalarTower (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq fun _ => by
    apply Subtype.ext
    change algebraMap (RatFuncInfinityIntegers K) L _ =
      algebraMap M L (algebraMap (RatFuncInfinityIntegers K) M _)
    exact IsScalarTower.algebraMap_apply (RatFuncInfinityIntegers K) M L _

local instance infinityPlaceTowerTopIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
  Algebra.IsIntegral.tower_top (RatFuncInfinityIntegers K)

local instance infinityPlaceTowerFaithful :
    FaithfulSMul (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply Subtype.ext
  apply (algebraMap M L).injective
  exact congrArg Subtype.val hxy

local instance infinityPlaceTowerRelativeModuleFinite :
    Module.Finite (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) :=
  Module.Finite.of_restrictScalars_finite (RatFuncInfinityIntegers K)
    (RatFuncInfinityIntegralClosure K M)
    (RatFuncInfinityIntegralClosure K L)

local instance infinityPlaceTowerIntermediateFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K M) M :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) M
    (RatFuncInfinityIntegralClosure K M)

local instance infinityPlaceTowerTopFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityPlaceTowerIntermediateClosureFieldTower :
    IsScalarTower (RatFuncInfinityIntegralClosure K M) M L :=
  inferInstance

local instance infinityPlaceTowerTopClosureFieldTower :
    IsScalarTower (RatFuncInfinityIntegralClosure K M)
      (RatFuncInfinityIntegralClosure K L) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def, map_mul]
    rw [show algebraMap (RatFuncInfinityIntegralClosure K L) L
        (algebraMap (RatFuncInfinityIntegralClosure K M)
          (RatFuncInfinityIntegralClosure K L) r) =
        algebraMap (RatFuncInfinityIntegralClosure K M) L r by rfl]
    ring⟩

local instance infinityPlaceTowerRelativeIsIntegralClosure :
    IsIntegralClosure (RatFuncInfinityIntegralClosure K L)
      (RatFuncInfinityIntegralClosure K M) L :=
  IsIntegralClosure.tower_top (R := RatFuncInfinityIntegers K)

section Galois

variable [IsGalois M L]

/-- Galois conjugacy of places above infinity, expressed on their prime
ideals. -/
def InfinityPlacesGaloisConjugate
    (P Q : FiniteExtensionInfinityPlace K L) : Prop :=
  letI := infinityIntegralClosureGalAction K M L
  ∃ g : Gal(L/M), Q.1 = g • P.1

end Galois
end
end BGS.HasseWeil
end
