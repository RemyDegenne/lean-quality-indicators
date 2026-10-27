@[expose] public section

open Module

open scoped Pointwise

variable (R S A B : Type*)

section AlgHomTower

variable {A} {C D : Type*} [CommSemiring A] [CommSemiring C] [CommSemiring D] [Algebra A C]
  [Algebra A D]

variable [CommSemiring B] [Algebra A B] [Algebra B C] [IsScalarTower A B C] (f : C →ₐ[A] D)

/-- Extend the scalars of an `AlgHom`. -/
def AlgHom.extendScalars : @AlgHom B C D _ _ _ _ (f.domRestrict B).toRingHom.toAlgebra where
  __ := f
  commutes' := fun _ ↦ rfl
  __ := (f.domRestrict B).toRingHom.toAlgebra

end AlgHomTower
end
