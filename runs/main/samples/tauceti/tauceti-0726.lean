public section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

universe u

theorem Scheme.Hom.isIso_app_of_isBasis {X Y : Scheme.{u}} (p : Y ⟶ X) {ι : Type*}
    {B : ι → X.Opens} (hB : Opens.IsBasis (Set.range B)) (h : ∀ i, IsIso (p.app (B i)))
    (U : X.Opens) : IsIso (p.app U) := by
  let φ : X.sheaf ⟶ (TopCat.Sheaf.pushforward _ p.base).obj Y.sheaf := ObjectProperty.homMk p.c
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis hB h
  have : IsIso ((TopCat.Sheaf.forget _ _).map φ) := Functor.map_isIso _ _
  exact NatIso.isIso_app_of_isIso ((TopCat.Sheaf.forget _ _).map φ) (op U)

end AlgebraicGeometry
end
