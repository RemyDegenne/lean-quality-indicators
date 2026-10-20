namespace P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_or

set_option autoImplicit false

p2m_open

namespace ModularCurve

namespace DRModelPackage

namespace SpecialFibreMax

p2m_open

section Local

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] (toκ : O →+* κ)

theorem isPullback_baseChangeMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    IsPullback (DRModel.baseChangeMap (p := p) φ)
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ B))))
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have hρι : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show φ.comp (algebraMap ℤ A) = algebraMap ℤ B from RingHom.ext_int _ _]
  have h2 : DRModel.baseChangeMap (p := p) φ ≫ pullback.snd (DRModel.toBase p) _ =
      pullback.snd (DRModel.toBase p) _ ≫ Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _
  refine IsPullback.of_right ?_ h2
    (IsPullback.of_hasPullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))))
  have h1 : DRModel.baseChangeMap (p := p) φ ≫ pullback.fst (DRModel.toBase p) _ =
      pullback.fst (DRModel.toBase p) _ := by
    rw [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  convert IsPullback.of_hasPullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ B))) using 1

end Local
end SpecialFibreMax
end DRModelPackage
end ModularCurve
end P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_or
