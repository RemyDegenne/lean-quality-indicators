public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace FiniteLocallyFreeSheaf

variable (X : Scheme.{u})

variable {X}

variable (X) in
/-- In rank zero the determinant is naturally the trivial invertible sheaf: `⋀⁰ E ≅ 𝒪_X`. -/
def determinantZeroIso :
    determinant X 0 ≅ (Functor.const _).obj (InvertibleSheaf.trivial X) :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _
      ((SheafOfModules.exteriorPowerZeroIso X.sheaf).app E.obj.obj ≪≫
        (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf).symm ≪≫
        eqToIso (InvertibleSheaf.trivial_obj X).symm))
    (fun f ↦ by
      -- As for `determinantOneIso`, this is the naturality of `exteriorPowerZeroIso`; the
      -- constant functor acts on morphisms by identities.
      ext1
      exact ((SheafOfModules.exteriorPowerZeroIso X.sheaf).hom.naturality_assoc f.hom.hom _).trans
        (Category.comp_id _).symm)

end FiniteLocallyFreeSheaf
end
end AlgebraicGeometry
end TauCeti
end
