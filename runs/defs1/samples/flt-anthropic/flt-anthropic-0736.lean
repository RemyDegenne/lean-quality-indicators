namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero

set_option autoImplicit false

universe u

p2m_open

noncomputable section

set_option autoImplicit false

section

p2m_open

namespace AlgebraicGeometry

namespace OModulePresheaf

namespace Leray

namespace RelHZero

p2m_open

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}

variable (K' : Scheme.OrderedAffineCover V')

variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) (U : Z.Opens)

def relHZeroHom :
    OModulePresheaf.Hom (relHPresheaf p πZ K' 0) (pullOpen p πZ (⊤ : V'.Opens)) where
  app U := (relHEquiv K' p πZ U).toLinearMap
  app_smul U a z := by
    obtain ⟨w, rfl⟩ := (toRelH_bijective K' p πZ U).2 z
    show relHEquiv K' p πZ U (a • toRelH K' p πZ U w) = a • relHEquiv K' p πZ U (toRelH K' p πZ U w)
    rw [← toRelH_smul, relHEquiv_toRelH, relHEquiv_toRelH]
  naturality {U U'} h := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨w, rfl⟩ := (toRelH_bijective K' p πZ U').2 z
    show relHEquiv K' p πZ U ((relHPresheaf p πZ K' 0).res h (toRelH K' p πZ U' w))
      = (pullOpen p πZ (⊤ : V'.Opens)).res h (relHEquiv K' p πZ U' (toRelH K' p πZ U' w))
    rw [← toRelH_res, relHEquiv_toRelH, relHEquiv_toRelH]

end RelHZero
end Leray
end OModulePresheaf
end AlgebraicGeometry
end
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero
