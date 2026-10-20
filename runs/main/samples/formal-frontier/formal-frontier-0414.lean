@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace KTheory.K0

variable (R : Type uR) [CommRing R]

@[simp]
theorem ofClassRingHom_apply (a : ProjectiveClass R) :
    ofClassRingHom R a = ofClass R a := rfl

end KTheory.K0
end
