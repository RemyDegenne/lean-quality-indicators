@[expose] public section

open Module

variable {R : Type*} [Semiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable {M' : Type*} [AddCommGroup M'] [Module R M']

variable {N' : Type*} [AddCommGroup N'] [Module R N']

variable {ι ι' ι'' : Type*}

@[inherit_doc]
notation M " [⋀^" ι "]→ₗ[" R "] " N:100 => AlternatingMap R M N ι

namespace AlternatingMap

variable (f f' : M [⋀^ι]→ₗ[R] N)

variable (g g₂ : M [⋀^ι]→ₗ[R] N')

variable (g' : M' [⋀^ι]→ₗ[R] N')

variable (v : ι → M) (v' : ι → M')

open Function

@[simp]
theorem map_update_neg [DecidableEq ι] (i : ι) (x : M') :
    g' (update v' i (-x)) = -g' (update v' i x) :=
  g'.toMultilinearMap.map_update_neg v' i x

end AlternatingMap
end
