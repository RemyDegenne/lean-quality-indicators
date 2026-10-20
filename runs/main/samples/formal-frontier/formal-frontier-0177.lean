@[expose] public section

universe u v w

namespace FundamentalGroup

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

open CategoryTheory

theorem fundamentalGroupMulEquivOfPath_comp_map_of_homotopy {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (x : X) :
    (fundamentalGroupMulEquivOfPath (H.evalAt x)).toMonoidHom.comp (map f x) = map g x :=
  MonoidHom.ext fun γ => fundamentalGroupMulEquivOfPath_map_of_homotopy H x γ

end FundamentalGroup
end
