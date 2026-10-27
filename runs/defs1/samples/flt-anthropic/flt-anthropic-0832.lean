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

noncomputable def piPowι (i : Fin n) : SheafOfModules.unit X.ringCatSheaf ⟶ piPow X n :=
  ⟨PresheafOfModules.homMk (M₁ := PresheafOfModules.unit _)
    { app := fun V => AddCommGrpCat.ofHom (X := (X.presheaf.obj V : Type u))
        (Y := Fin n → (X.presheaf.obj V : Type u))
        (AddMonoidHom.single (fun _ : Fin n => (X.presheaf.obj V : Type u)) i)
      naturality := fun V W g => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun (a : X.presheaf.obj V) => ?_)
        funext k
        change (Pi.single i (X.presheaf.map g a) : Fin n → X.presheaf.obj W) k =
          X.presheaf.map g ((Pi.single i a : Fin n → X.presheaf.obj V) k)
        simp only [Pi.single_apply]
        split_ifs <;> simp }
    (fun V (r : X.presheaf.obj V) (a : X.presheaf.obj V) => by
      funext k
      change (Pi.single i (r * a) : Fin n → X.presheaf.obj V) k =
        r * (Pi.single i a : Fin n → X.presheaf.obj V) k
      simp only [Pi.single_apply]
      split_ifs <;> simp)⟩

end Modules
end Scheme
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis
