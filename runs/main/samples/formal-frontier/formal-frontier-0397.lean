@[expose] public section

open Filter Set

set_option linter.style.haveILetI false

namespace AdicCompletion

universe u

@[simp]
theorem abstractCompletion_coe
    {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) :
    (abstractCompletion I hI hfg).coe = algebraMap R (AdicCompletion I R) :=
  rfl

end AdicCompletion
end
