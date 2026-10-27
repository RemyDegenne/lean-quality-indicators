@[expose] public section

universe u v w

variable {S T : Type*}

variable {R : Type*} {M N P A : Type*}

open LinearMap (BilinMap BilinForm)

namespace QuadraticMap

section restrictScalars

variable [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [Module S M] [Module S N] [Algebra S R]

variable [IsScalarTower S R M] [IsScalarTower S R N]

/-- If `Q : M → N` is a quadratic map of `R`-modules and `R` is an `S`-algebra,
then the restriction of scalars is a quadratic map of `S`-modules. -/
@[simps!]
def restrictScalars (Q : QuadraticMap R M N) : QuadraticMap S M N where
  toFun x := Q x
  toFun_smul a x := by
    simp [map_smul_of_tower]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.restrictScalars₁₂ (S := R) (R' := S) (S' := S), fun x y => by
      simp only [LinearMap.restrictScalars₁₂_apply_apply, h]⟩

end restrictScalars
end QuadraticMap
end
