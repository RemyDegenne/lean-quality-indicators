namespace P2MW.S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace P2mIdxOne

open IsLocalRing

section Field

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]

theorem isRegularLocalRing_localization_of_smooth [Algebra.Smooth k B] (q : Ideal B) [hq : q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    show (algebraMap k B).Smooth
    rw [RingHom.Smooth]
    convert (inferInstance : Algebra.Smooth k B)
    exact Algebra.algebra_ext _ _ fun _ => rfl
  have h := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk
    (f := Spec.map (CommRingCat.ofHom (algebraMap k B))) (⟨q, hq⟩ : PrimeSpectrum B)
  exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _
    (AlgebraicGeometry.StructureSheaf.stalkIso B (⟨q, hq⟩ : PrimeSpectrum B)).toRingEquiv.symm

end Field
end P2mIdxOne
end P2MW.S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
