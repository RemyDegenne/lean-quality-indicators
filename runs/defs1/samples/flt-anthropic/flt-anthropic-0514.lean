set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type u}

open GlueOfCocycle

namespace GlueOfCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U) (T : X.Opens)

variable {c T}

variable (c T)

variable {T}

noncomputable def preGlue : (Opens X)ᵒᵖ ⥤ Ab where
  obj T := AddCommGrpCat.of (families c T.unop)
  map {T T'} f := AddCommGrpCat.ofHom (resFam c f.unop.le)
  map_id T := by
    ext
    exact rO_refl _
  map_comp {T₁ T₂ T₃} f g := by
    ext
    exact (rO_rO _ _ _).symm

end GlueOfCocycle
end AlgebraicGeometry.Scheme.Modules
