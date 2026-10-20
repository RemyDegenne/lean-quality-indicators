namespace P2MW.S_Module_free_of_torsionBySet_eq_annihilator_smul

set_option autoImplicit false

universe u v w x

namespace M4cP4NCMOD3

open Module Submodule Pointwise

section Ring

variable {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [CommRing T] [Algebra 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)

theorem πT_surjective : Function.Surjective πT :=
  fun c => ⟨algebraMap 𝒪 T c, πT.commutes c⟩

end Ring
end M4cP4NCMOD3
end P2MW.S_Module_free_of_torsionBySet_eq_annihilator_smul
