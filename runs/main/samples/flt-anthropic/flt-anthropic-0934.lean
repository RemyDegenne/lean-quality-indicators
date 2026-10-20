namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_transition_mul_mul

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace PV6R1

variable {Y : Scheme.{u}}

theorem opHom_eq {A B : (Y.Opens)ᵒᵖ} (f g : A ⟶ B) : f = g :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

end PV6R1
end P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_transition_mul_mul
