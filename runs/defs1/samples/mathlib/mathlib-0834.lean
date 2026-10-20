@[expose] public section

variable {G α β ι : Type*}

open Filter

open scoped Topology NNReal

attribute [instance 10] NonUnitalSeminormedRing.toNonUnitalRing

attribute [instance 10] SeminormedRing.toRing

attribute [instance 10] NonUnitalNormedRing.toNonUnitalRing

attribute [instance 10] NormedRing.toRing

attribute [instance 10] NonUnitalSeminormedCommRing.toNonUnitalCommRing

attribute [instance 10] NonUnitalNormedCommRing.toNonUnitalCommRing

attribute [instance 10] SeminormedCommRing.toCommRing

attribute [instance 10] NormedCommRing.toCommRing

section IsUnital

attribute [local instance] IsUnital.toMulOneClass in
/-- A unital non-unital seminormed ring is a seminormed ring.

This constructor is primarily intended to be used within proofs since it creates bad definitional
equalities. -/
noncomputable abbrev IsUnital.toSeminormedRing {A : Type*} [NonUnitalSeminormedRing A]
    [IsUnital A] : SeminormedRing A where
  __ := ‹NonUnitalSeminormedRing A›
  __ := toSemiring

end IsUnital
end
