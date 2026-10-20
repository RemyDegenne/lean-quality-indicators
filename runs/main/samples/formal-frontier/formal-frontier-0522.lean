@[expose] public section

universe u v w

namespace FundamentalGroup

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

open CategoryTheory

theorem fundamentalGroupMulEquivOfPath_map_of_homotopy {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (x : X) (γ : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfPath (H.evalAt x) (map f x γ) = map g x γ := by
  change Groupoid.inv ((FundamentalGroupoidFunctor.homotopicMapsNatIso H).app
      (FundamentalGroupoid.mk x)) ≫ (FundamentalGroupoid.map f).map γ ≫
        (FundamentalGroupoidFunctor.homotopicMapsNatIso H).app (FundamentalGroupoid.mk x) =
      (FundamentalGroupoid.map g).map γ
  rw [Groupoid.inv_eq_inv]
  exact NatIso.naturality_1' (FundamentalGroupoidFunctor.homotopicMapsNatIso H) γ

end FundamentalGroup
end
