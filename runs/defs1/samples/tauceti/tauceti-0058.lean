public section

noncomputable section

universe v

namespace TauCeti.FarguesFontaine

open CategoryTheory CategoryTheory.Limits Opposite _root_.TopologicalSpace Topology

open TauCeti.Huber TauCeti.ValuationSpectrum _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type v} [CommRing R] [TopologicalSpace (WittVector p R)]
  [CharP R p] [PerfectRing R p] {ϖ : R}

section Wandering

variable [IsTopologicalRing (WittVector p R)] (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))

/-- **Restriction from `𝒪_𝒳(q V)` to `𝒪_𝒴(V)`** for an open `V ⊆ 𝒴`: a section of `𝒪_𝒳` over
the open image `q V` is a Frobenius-invariant section of `𝒪_𝒴` over `q⁻¹(q V) ⊇ V`, and this map
restricts it to `V`. -/
def spaXPresheafRestrict (V : Opens (spaY p ϖ)) :
    (spaXPresheaf P hI).obj (op ((IsOpenMap.functor (f := quotientTopHom hI)
      (isOpenQuotientMap_quotientMap hI).isOpenMap).obj V)) ⟶ (spaYPresheaf P ϖ).obj (op V) :=
  (spaXPresheafι P hI).app _ ≫
    (spaYPresheaf P ϖ).map ((IsOpenMap.adjunction (f := quotientTopHom hI)
      (isOpenQuotientMap_quotientMap hI).isOpenMap).unit.app V).op

end Wandering
end TauCeti.FarguesFontaine
end
end
