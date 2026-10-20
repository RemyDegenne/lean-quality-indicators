@[expose] public section

universe u u' v w w'

section Adjoin

universe uR uS uA uB

open Submodule Subsemiring

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

macro_rules (kind := subalgebra_adjoin)
  | `($R[$xs,*]) => `(Algebra.adjoin $R {$xs:term,*})
  | `($R[$xs,* : $A]) => do
    let xs' ← xs.getElems.mapM fun x => `(($x : $A))
    `(Algebra.adjoin $R ({$[$xs':term],*} : Set $A))

open Algebra Subalgebra

namespace AlgHom

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem map_adjoin (φ : A →ₐ[R] B) (s : Set A) : (adjoin R s).map φ = adjoin R (φ '' s) :=
  (adjoin_image _ _ _).symm

end AlgHom
end Adjoin
end
