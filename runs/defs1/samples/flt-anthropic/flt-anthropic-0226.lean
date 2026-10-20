namespace P2MW.S_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open TensorProduct CategoryTheory Algebra.DescentCofaces

universe u

namespace S17C1

section Dictionary

open ChangeOfRings

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (N : Type u) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

noncomputable abbrev Nc : ModuleCat.{u} B := ModuleCat.of B N

end Dictionary
end S17C1
end P2MW.S_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle
