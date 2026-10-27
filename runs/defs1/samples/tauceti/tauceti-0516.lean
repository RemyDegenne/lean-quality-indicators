public section

noncomputable section

universe v

namespace TauCeti.FarguesFontaine

open AlgebraicGeometry _root_.CategoryTheory Opposite _root_.TopologicalSpace Topology

open TauCeti.Huber TauCeti.ValuationSpectrum _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type v} [CommRing R] [TopologicalSpace (WittVector p R)]
  [IsTopologicalRing (WittVector p R)] {ϖ : R}
  (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))

variable [CharP R p] [PerfectRing R p]

section Desc

open CategoryTheory.Limits

variable {P hI} {W : PresheafedSpace CompleteSeparatedTopCommRingCat.{v}}
  {g : (spaYPreAdicSpace P hI).toPresheafedSpace ⟶ W}

variable (P hI) in
/-- **`𝒳` is the coequalizer of the identity and Frobenius on `𝒴`** in presheafed spaces of complete
separated topological rings, with the projection `q` as coprojection. -/
def isColimitQuotientPresheafedCofork :
    IsColimit (Cofork.ofπ (f := 𝟙 _) (g := (spaYFrobenius P hI).toHom)
      (quotientPresheafedHom P hI)
      ((Category.id_comp _).trans (spaYFrobenius_toHom_comp_quotientPresheafedHom P hI).symm)) :=
  Cofork.IsColimit.mk _
    (fun s ↦ quotientPresheafedDesc s.π (by simpa using s.condition.symm))
    (fun s ↦ quotientPresheafedHom_comp_quotientPresheafedDesc _)
    (fun s m hm ↦ quotientPresheafedHom_hom_ext
      (hm.trans (quotientPresheafedHom_comp_quotientPresheafedDesc _).symm))

end Desc
end TauCeti.FarguesFontaine
end
end
