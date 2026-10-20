@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

open scoped Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance regularConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance regularConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance regularInfinityNonempty : Nonempty (FiniteExtensionInfinityPlace K L) := by
  let : Algebra (RatFuncInfinityIntegers K) L :=
    Algebra.ofSubsemiring (RatFuncInfinityIntegers K)
  let : SMul (RatFuncInfinityIntegers K) L := Algebra.toSMul
  let : Module (RatFuncInfinityIntegers K) L := Algebra.toModule
  let _ : Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
    IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L
  let _ : Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
    Module.IsTorsionFree.trans_faithfulSMul
      (RatFuncInfinityIntegers K) (RatFunc K) L
  let _ : Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
    IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L
  exact Ideal.nonempty_primesOver (ratFuncInfinityPlace K).asIdeal

local instance regularPlaceNonempty : Nonempty (FiniteExtensionPlace K L) :=
  Nonempty.map Sum.inr (regularInfinityNonempty K L)

theorem finiteExtensionRiemannSpace_zero_finrank
    (hconstants : algebraicClosure K L = ⊥) :
    Module.finrank K (finiteExtensionRiemannSpace K L 0) = 1 := by
  rw [finiteExtensionRiemannSpace_zero_eq_range K L hconstants]
  have hinjective : Function.Injective (Algebra.linearMap K L) :=
    (algebraMap K L).injective
  let e : K ≃ₗ[K] LinearMap.range (Algebra.linearMap K L) :=
    LinearEquiv.ofInjective (Algebra.linearMap K L) hinjective
  calc
    Module.finrank K (LinearMap.range (Algebra.linearMap K L)) =
        Module.finrank K K := e.finrank_eq.symm
    _ = 1 := Module.finrank_self K

end
end BGS.HasseWeil
end
