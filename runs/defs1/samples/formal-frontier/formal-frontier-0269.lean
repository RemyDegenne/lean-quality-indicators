public section

set_option warningAsError true

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace

namespace TopCat.Sheaf.AbelianForget

variable {X Y : TopCat.{v}} (g : X ⟶ Y)

/-- The natural isomorphism whose forward map is the canonical adjunction mate. -/
@[expose] noncomputable def canonicalComparisonIso :
    underlyingSheaf Y ⋙ TopCat.Sheaf.pullback (Type v) g ≅
      TopCat.Sheaf.pullback AddCommGrpCat.{v} g ⋙ underlyingSheaf X :=
  NatIso.ofComponents (fun A =>
    @asIso _ _ _ _ (canonicalComponent g A) (canonicalComponent_isIso g A))
    (fun {_ _} a => canonicalComponent_naturality g a)

end TopCat.Sheaf.AbelianForget
end
