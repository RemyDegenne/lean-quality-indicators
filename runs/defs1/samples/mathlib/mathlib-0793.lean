@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

variable {R : Type u} {A : Type v} {B : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

section

variable (R A) in
/-- An `R`-algebra `A` is formally etale if both `Ω[A⁄R]` and `H¹(L_{A/R})` are zero.
For the infinitesimal lifting definition, see `FormallyEtale.iff_comp_bijective`. -/
@[mk_iff, stacks 00UQ]
class FormallyEtale : Prop where
  subsingleton_kaehlerDifferential : Subsingleton Ω[A⁄R]
  subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)

end
end Algebra
end
