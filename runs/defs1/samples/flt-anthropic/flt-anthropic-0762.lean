namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice_anyResidueField

set_option autoImplicit false

p2m_open

universe u

noncomputable section

namespace E160A3

p2m_open

section Coords

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  {A P : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (qP : P ⟶ Spec (CommRingCat.of T'))
  (s : A ⟶ P) (hsq : s ≫ qP = f)

def sliceAlgHom (W : P.Opens) :
    letI := algebraOfHom qP W
    letI := algebraOfHom f (s ⁻¹ᵁ W)
    Γ(P, W) →ₐ[T'] Γ(A, s ⁻¹ᵁ W) :=
  letI := algebraOfHom qP W
  letI := algebraOfHom f (s ⁻¹ᵁ W)
  { toRingHom := (s.appLE W (s ⁻¹ᵁ W) le_rfl).hom
    commutes' := fun r => by
      change (qP.appLE ⊤ W le_top ≫ s.appLE W (s ⁻¹ᵁ W) le_rfl).hom ((Scheme.ΓSpecIso (CommRingCat.of T')).inv.hom r) =
        (f.appLE ⊤ (s ⁻¹ᵁ W) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of T')).inv.hom r)
      rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hsq ⊤ (s ⁻¹ᵁ W) _ le_top] }

end Coords
end E160A3
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_isTangentCoordsOfPairAt_slice_anyResidueField
