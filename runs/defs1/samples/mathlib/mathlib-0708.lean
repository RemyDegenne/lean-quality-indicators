@[expose] public section

open Function Module

namespace LinearMap

section CommSemiring

variable {R M M' N N' : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M']
  [AddCommMonoid N'] [CommSemiring R] [Module R M] [Module R M'] [Module R N] [Module R N']
  {p : M →ₗ[R] N →ₗ[R] R} {x : M} {y : N}

variable [p.IsPerfPair]

variable (p)

/-- Turn a perfect pairing between `M` and `N` into an isomorphism between `M` and the dual of `N`.
-/
noncomputable def toPerfPair : M ≃ₗ[R] Dual R N :=
  .ofBijective { toFun := _, map_add' x y := by simp, map_smul' r x := by simp } <|
    IsPerfPair.bijective_left p

end CommSemiring
end LinearMap
end
