public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

open CategoryTheory WithConv

namespace TauCeti

universe u v w w'

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

lemma mapPoints_liftQuotientPoint (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) {A B : CommAlgCat.{w} R}
    (χ : A ⟶ B) (g : HopfAlgebra.points (R := R) (H := H) A)
    (hg : ∀ h : H, h ∈ I → g.ofConv h = 0) :
    HopfAlgebra.mapPoints (H := quotient H I) χ
        (liftQuotientPoint H I A g hg) =
      liftQuotientPoint H I B (HopfAlgebra.mapPoints (H := H) χ g)
        (by
          intro h hh
          exact (mem_quotientPointsSubgroup_iff H I B _).mp
            (mapPoints_mem_quotientPointsSubgroup H I χ
              ((mem_quotientPointsSubgroup_iff H I A g).mpr hg)) h hh) := by
  apply quotientPointsHom_injective H I B
  rw [← mapPoints_quotientPointsHom H I χ, quotientPointsHom_liftQuotientPoint,
    quotientPointsHom_liftQuotientPoint]

end CommHopfAlgCat
end TauCeti
end
