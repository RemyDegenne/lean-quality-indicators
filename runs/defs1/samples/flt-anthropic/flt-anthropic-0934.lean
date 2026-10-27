namespace P2MW.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one

set_option autoImplicit false

universe u

open TensorProduct

noncomputable section

namespace P2mTwoTermH0Ann

variable {R : Type u} [CommRing R]

section Coordinates

open scoped Classical

open Matrix

variable (G : CoherentBaseChange.TwoTermComplex.{u, u} R)

abbrev ι1 : Type u := Module.Free.ChooseBasisIndex R G.C1

end Coordinates
end P2mTwoTermH0Ann
end
end P2MW.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one
