@[expose] public section

open Module Polynomial Submodule

section

variable {R A B S : Type*}

variable [CommRing R] [CommRing A] [Ring B] [CommRing S]

variable [Algebra R A] [Algebra R B] {f : R →+* S}

variable (f : R →+* S) (R A)

variable {R A}

theorem RingHom.IsIntegralElem.of_mul_unit (x y : S) (r : R) (hr : f r * y = 1)
    (hx : f.IsIntegralElem (x * y)) : f.IsIntegralElem x :=
  letI : Algebra R S := f.toAlgebra
  IsIntegral.of_mul_unit hr hx

end
end
