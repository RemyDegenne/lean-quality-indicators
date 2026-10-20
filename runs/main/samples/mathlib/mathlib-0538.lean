@[expose] public section

universe u v w z

variable {R S : Type*} [CommRing R] [CommRing S]

variable [Algebra R S]

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable {ι κ : Type w}

open Module

open LinearMap (BilinForm)

open LinearMap

open Matrix

open scoped Matrix

variable {F : Type*} [Field F]

variable [Algebra R L] [Algebra L F] [Algebra R F] [IsScalarTower R L F]

open Polynomial

attribute [-instance] Field.toEuclideanDomain

section DetNeZero

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z)

variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

open Finset

@[simp]
theorem traceMatrix_apply (b : κ → B) (i j) : traceMatrix A b i j = traceForm A B (b i) (b j) :=
  rfl

end Algebra
end DetNeZero
end
