namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq

set_option autoImplicit false

p2m_open

universe u

noncomputable section

namespace Sub2c

section Twist

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

noncomputable def twist {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t) :
    RigidifiedLineBundle c ε₂ t where
  L := M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M)
  isInvertible := M.isInvertible.tensor ((qinv_isInvertible ε₁ ε₂ M).pullback _)
  rigidified := ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    whiskerLeftIso _ (sectionPullbackIso t ε₂ _) ≪≫ qinvIso ε₁ ε₂ M⟩

end Twist
end Sub2c
end
end P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq
