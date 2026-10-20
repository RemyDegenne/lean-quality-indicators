namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_ofPoint_of_range_subset

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace SectInvAux

scoped instance {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (V : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : IsOpenImmersion (jV c V t) := by
  dsimp only [jV]; infer_instance

lemma jV_snd {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (V : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : jV c V t ≫ pullback.snd c t = pullback.snd _ _ ≫ 𝟙 T :=
  pullback.lift_snd _ _ _

end SectInvAux
end P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_ofPoint_of_range_subset
