@[expose] public section

universe a w p

open CategoryTheory

open scoped Simplicial

namespace SSet.Homotopy

variable {S T : SSet.{w}} {f g : S ⟶ T}

/-- A cylinder homotopy gives a homotopy of the original normalized integral
tensor maps through its combinatorial simplicial homotopy. -/
noncomputable def tensorNormalizedChainComplexMap
    (H : SSet.Homotopy f g) (A : Type a) [AddCommGroup A] :
    _root_.Homotopy (SSet.tensorNormalizedChainComplexMap.{a, w, p} A f)
      (SSet.tensorNormalizedChainComplexMap.{a, w, p} A g) :=
  H.toSimplicialObjectHomotopy.tensorNormalizedChainComplexMap.{a, w, p} A

end SSet.Homotopy
end
