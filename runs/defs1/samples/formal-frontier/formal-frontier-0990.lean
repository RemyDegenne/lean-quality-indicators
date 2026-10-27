@[expose] public section

universe uR uS uT uM uN

open CategoryTheory

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable {M : Type uM} {N : Type uN}

variable [AddCommGroup M] [Module Rᵐᵒᵖ M]

variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

section SemilinearHomEquiv

universe uX

variable {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X]

/-- The additive extension/restriction correspondence for right modules over
arbitrary, possibly noncommutative rings. -/
def linearMapAddEquiv : (Obj f M →ₗ[Sᵐᵒᵖ] X) ≃+ (M →ₛₗ[RingHom.op f] X) where
  __ := linearMapEquiv f
  map_add' g h := by
    apply LinearMap.ext
    intro m
    rfl

end SemilinearHomEquiv
end ModuleCat.RightExtension
end
