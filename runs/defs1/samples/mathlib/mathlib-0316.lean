@[expose] public section

open scoped TensorProduct

open Algebra.Extension KaehlerDifferential MvPolynomial

universe u v w

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

variable {B P C : Type*} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing P] [Algebra R P]

namespace Algebra

section

variable (R A) in
/--
An `R`-algebra `A` is formally smooth if `Ω[A⁄R]` is `A`-projective and `H¹(L_{A/R}) = 0`.
For the infinitesimal lifting definition,
see `FormallySmooth.lift` and `FormallySmooth.iff_comp_surjective`.
-/
@[stacks 00TI "Also see 031J (6) for the equivalence with the definition given here.", mk_iff]
class FormallySmooth : Prop where
  projective_kaehlerDifferential : Module.Projective A Ω[A⁄R]
  subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)

end
end Algebra
end
