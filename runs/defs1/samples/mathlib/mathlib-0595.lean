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

namespace MultilinearMap

open Equiv

variable [Fintype ι] [DecidableEq ι]

/-- Produce an `AlternatingMap` out of a `MultilinearMap`, by summing over all argument
permutations. -/
def alternatization : MultilinearMap R (fun _ : ι => M) N' →+ M [⋀^ι]→ₗ[R] N' where
  toFun m :=
    { ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ with
      toFun := ⇑(∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ)
      map_eq_zero_of_eq' := private fun v i j hvij hij =>
        alternatization_map_eq_zero_of_eq_aux m v i j hij hvij }
  map_add' a b := by ext; simp [Finset.sum_add_distrib]
  map_zero' := by ext; simp

end MultilinearMap
end
