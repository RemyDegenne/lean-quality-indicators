public section

open CategoryTheory TensorProduct WithConv

open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} {V : Type w} [CommRing R] [CommRing H]

variable [_root_.HopfAlgebra R H]

variable [AddCommMonoid V] [Module R V]

namespace PointRepresentation

/-- The natural point representation induced by a right `H`-comodule structure. -/
noncomputable def ofComodule (rho : Comodule R H V) :
    PointRepresentation (R := R) (H := H) (V := V) where
  app A := rawPointAction rho A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm
  naturality A B phi := by
    -- `pointsFunctor_obj` and the scalar-extension object theorem are categorical equalities,
    -- with no computation lemma that rewrites this structure-field goal before it is exposed.
    change
      mapPoints (H := H) phi ≫ rawPointAction rho B ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) B).symm =
        rawPointAction rho A ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm ≫
          (GeneralLinear.scalarExtensionAutomorphismsFunctor (V := V)).map phi
    have hraw :
        mapPoints (H := H) phi ≫ rawPointAction rho B =
          rawPointAction rho A ≫
            GeneralLinear.mapScalarExtensionAutomorphisms (V := V) phi := by
      apply GrpCat.ext
      intro x
      exact (rawPointAction_naturality rho phi x).symm
    rw [GeneralLinear.scalarExtensionAutomorphismsFunctor_map]
    rw [← Category.assoc, hraw]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end PointRepresentation
end HopfAlgebra
end TauCeti
end
