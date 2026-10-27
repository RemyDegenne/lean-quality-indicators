@[expose] public section

universe u

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

namespace Algebra

variable {A} in
/--
An `R`-algebra `A` is smooth at a prime `p` of `A` if `Aₚ` is formally smooth over `R`.

This does not imply `Aₚ` is smooth over `R` under the mathlib definition
even if `A` is finitely presented,
but it can be shown that this is equivalent to the stacks project definition that `A` is smooth
at `p` if and only if there exists `f ∉ p` such that `A_f` is smooth over `R`.
See `Algebra.basicOpen_subset_smoothLocus_iff_smooth` and `Algebra.isOpen_smoothLocus`.
-/
@[stacks 00TB]
abbrev IsSmoothAt (p : Ideal A) [p.IsPrime] : Prop :=
  Algebra.FormallySmooth R (Localization.AtPrime p)

end Algebra
end
