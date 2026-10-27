@[expose] public section

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u u' v w

variable {ι : Type u} {ι' : Type u'} (R : Type*) {S : Type v} {A : Type w}

variable {x : ι → A} {y : ι' → A}

variable [CommRing R] [CommRing S] [CommRing A]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

open AlgebraicIndependent

variable (A)

variable {A}

variable {R}

variable (ι R)

variable {ι R}

namespace AlgebraicIndependent

variable (R A) [FaithfulSMul R A]

section

variable [NoZeroDivisors A]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `R` is a commutative ring and `A` is a commutative `R`-algebra with injective algebra map
and no zero-divisors, then the `R`-algebraic independent subsets of `A` form a matroid. -/
def matroid : Matroid A := (indepMatroid R A).matroid.copyBase univ
  (fun s ↦ IsTranscendenceBasis R ((↑) : s → A)) rfl
  (fun B ↦ by simp_rw [Matroid.isBase_iff_maximal_indep, isTranscendenceBasis_iff_maximal]; rfl)

end
end AlgebraicIndependent
end
end
