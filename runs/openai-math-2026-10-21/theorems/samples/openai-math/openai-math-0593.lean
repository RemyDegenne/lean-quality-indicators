namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder OnePoint

namespace PeakingPairData

variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C) (ι : A →⋆ₐ[ℂ] C)
  (hp : ∀ i n, ι (B.peak i n) = D.peak i n) (F : C →L[ℂ] A)
  (hfix : ∀ a, F (ι a) = a)
  (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp F))
  (hleft : ∀ a x, F (ι a*x) = a*F x) (hright : ∀ x a, F (x*ι a) = F x*a)
  (ht : ∀ x, B.trace (F x) = D.trace x)

include hp hfix hstate hleft hright ht in

theorem turnCentered_of_expectation_zero (x : C) (hx : F x = 0)
    (i : Bool) (a b : A) : D.turnCentered i (ι a*x*ι b) := by
  change (D.input false).expectation (!i) (ι a*x*ι b) = 0
  rw [B.expectation_composite D ι hp F hfix hstate hleft hright ht,hright,hleft,hx,mul_zero,zero_mul,map_zero]

end PeakingPairData
end NaimarkZFC
end
end OAI
