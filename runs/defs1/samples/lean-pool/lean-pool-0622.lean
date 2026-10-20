@[expose] public section

open MeasureTheory

namespace NRR

open Geometry

namespace IteratedRefinement

/-- Specialize the shared model-independent iteration to the fixed Fox--Neuwirth model. -/
noncomputable def build
    {K : Geometry.ConvexBody Plane}
    (H : PrimeRefinementTheorem)
    (ps : List PrimeFactor)
    (A : ℝ) (hA : 0 < A) (hAK : A ≤ K.area)
    (φ : NiceMV (BodySpace K (primeDescendArea A ps))) :
    IteratedRefinement ps A hA φ :=
  FlexibleIteratedRefinement.build H.toFlexible ps A hA hAK φ

end IteratedRefinement
end NRR
end
