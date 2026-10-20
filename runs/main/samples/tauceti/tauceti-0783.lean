public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial IsLocalRing

universe u

namespace WeierstrassCurve

section CommRing

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem SpecMap_chartι {A : CommRingCat.{u}} {i : Fin 3}
    (α : CommRingCat.of (W.toProjective.ChartRing i) ⟶ A) :
    Spec.map α ≫ W.chartι i =
      W.projModelPoint (α.hom.comp (algebraMap R _)) (P := α.hom ∘ W.toProjective.chartPoint i)
        (by simpa only [Projective.baseChange, WeierstrassCurve.baseChange,
          WeierstrassCurve.map_map] using (W.toProjective.equation_chartPoint i).map α.hom) (i := i)
        (by simpa only [Function.comp_apply, W.toProjective.chartPoint_self i, map_one] using
          isUnit_one) := by
  rw [W.chartι_eq_projModelPoint i]
  exact SpecMap_projModelPoint α.hom _

end CommRing
end WeierstrassCurve
end
