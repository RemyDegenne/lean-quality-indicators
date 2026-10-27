public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [LocallySmall.{w} C] {E : ExactStructure C} {P : ObjectProperty C}
  [ObjectProperty.EssentiallySmall.{w} P]

namespace ExactStructure

section

variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts]

local instance : P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

section EulerClassOf

variable (hproj : P ≤ E.isProjective)

local notation "hP" => E.isExtensionClosed_of_le_isProjective hproj

section ResolutionTheorem

variable [ObjectProperty.EssentiallySmall.{w} (E.admitsFiniteResolution P)]

/-- **The resolution theorem for finite projective resolutions.** When every object satisfying
`P` is `E`-projective, the inclusion of the full subcategory on `P` into the full subcategory of
objects admitting a finite `P`-resolution induces an isomorphism of exact Grothendieck groups.
Its inverse sends the class of an object to the alternating class of any finite `P`-resolution of
it, by `TauCeti.ExactStructure.resolutionEquiv_symm_of`. -/
noncomputable def resolutionEquiv :
    ExactK0 (E.fullSubcategory P hP) ≃+
      ExactK0 (E.fullSubcategory (E.admitsFiniteResolution P)
        (E.isExtensionClosed_admitsFiniteResolution hproj)) where
  toFun := ExactK0.map _ (E.isConflationExact_ιOfLE hP
    (E.isExtensionClosed_admitsFiniteResolution hproj) (E.le_admitsFiniteResolution P))
  invFun := E.eulerHom hproj
  map_add' _ _ := map_add _ _ _
  left_inv x := by
    refine DFunLike.congr_fun (ExactK0.hom_ext (f := (E.eulerHom hproj).comp
      (ExactK0.map _ (E.isConflationExact_ιOfLE hP
        (E.isExtensionClosed_admitsFiniteResolution hproj) (E.le_admitsFiniteResolution P))))
      (g := AddMonoidHom.id _)
      fun Y => ?_) x
    rw [AddMonoidHom.coe_comp, Function.comp_apply, ExactK0.map_of, E.eulerHom_of,
      E.eulerClassOf_of_prop hproj Y.property, AddMonoidHom.id_apply]
  right_inv x := by
    refine DFunLike.congr_fun (ExactK0.hom_ext
      (f := (ExactK0.map _ (E.isConflationExact_ιOfLE hP
        (E.isExtensionClosed_admitsFiniteResolution hproj) (E.le_admitsFiniteResolution P))).comp
          (E.eulerHom hproj))
      (g := AddMonoidHom.id _) fun Y => ?_) x
    rw [AddMonoidHom.coe_comp, Function.comp_apply, E.eulerHom_of, AddMonoidHom.id_apply,
      E.eulerClassOf_eq hproj Y.property ((E.admitsFiniteResolution_iff P).mp Y.property).some,
      E.map_eulerClassFullSubcategory_eq_of hproj]

end ResolutionTheorem
end EulerClassOf
end
end ExactStructure
end TauCeti
end
