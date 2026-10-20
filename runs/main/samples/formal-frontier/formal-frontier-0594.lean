public section

set_option warningAsError true

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

theorem isQuasicoherent_of_isOpenCover_presentation
    (X : Scheme.{u}) (M : X.Modules) {I : Type u}
    (U : I → X.Opens) (hU : IsOpenCover U)
    (P : ∀ i, (M.restrict (U i).ι).Presentation) :
    M.IsQuasicoherent := by
  let hqc (i : I) : (M.over (U i)).IsQuasicoherent :=
    (presentationOverOfPresentationRestrict X M (U i) (P i)).isQuasicoherent
  have hUTop : (Opens.grothendieckTopology X).CoversTop U := by
    rwa [Opens.coversTop_iff]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ M I U hUTop hqc

end AlgebraicGeometry.Scheme.Modules
end
