public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat Presheaf

universe u

namespace TopCat.Sheaf.IsQuasiFlasque

variable {X : TopCat.{u}} [QuasiSeparatedSpace X]

theorem epi_of_shortExact
    [CompactSpace X] [PrespectralSpace X]
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsQuasiFlasque S.X₁] : Epi (S.g.hom.app (op (⊤ : Opens X))) :=
  epi_app_of_shortExact hS ⊤ isCompact_univ

end TopCat.Sheaf.IsQuasiFlasque
end
end
