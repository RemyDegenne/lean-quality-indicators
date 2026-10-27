namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

universe u

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

p2m_open

open TopologicalSpace

variable (X : Scheme.{u}) (n : ℕ)

noncomputable def piPowBicone :
    Bicone (fun _ : ULift.{u} (Fin n) => SheafOfModules.unit X.ringCatSheaf) where
  pt := piPow X n
  π j := piPowπ X n j.down
  ι j := piPowι X n j.down
  ι_π j j' := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext
      (LinearMap.ext fun (a : X.presheaf.obj V) => ?_))
    by_cases h : j = j'
    · subst h
      rw [dif_pos rfl]
      change (Pi.single j.down a : Fin n → X.presheaf.obj V) j.down = a
      simp
    · rw [dif_neg h]
      have h' : j'.down ≠ j.down := fun e => h (ULift.ext _ _ e.symm)
      change (Pi.single j.down a : Fin n → X.presheaf.obj V) j'.down = (0 : X.presheaf.obj V)
      simp [h']

end Modules
end Scheme
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis
