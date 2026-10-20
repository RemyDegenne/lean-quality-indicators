@[expose] public section

open Set Function Polynomial

namespace Module

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

namespace AEval

variable (R M)

variable {R M}

section Submodule

variable (R M)

variable {R M}

variable (p : Submodule R M) (hp : p ∈ (Algebra.lsmul R R M a).invtSubmodule)

/-- The natural `R`-linear equivalence between the two ways to represent an invariant submodule. -/
def equiv_mapSubmodule :
    p ≃ₗ[R] mapSubmodule R M a ⟨p, hp⟩ where
  toFun x := ⟨of R M a x, by simp⟩
  invFun x := ⟨((of R M _).symm (x : AEval R M a)), by obtain ⟨x, hx⟩ := x; simpa using hx⟩
  map_add' x y := rfl
  map_smul' t x := rfl

end Submodule
end AEval
end Module
end
