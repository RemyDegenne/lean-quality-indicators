@[expose] public section

universe u v w

namespace FundamentalGroup

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

open CategoryTheory

theorem map_fundamentalGroupMulEquivOfPath (f : C(X, Y)) {x x' : X}
    (a : Path x x') (γ : FundamentalGroup X x) :
    map f x' (fundamentalGroupMulEquivOfPath a γ) =
      fundamentalGroupMulEquivOfPath (a.map f.continuous) (map f x γ) := by
  calc
    _ = ((FundamentalGroupoid.map f).mapIso
        ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
          (FundamentalGroupoid.mk x')).symm
            (Path.Homotopic.Quotient.mk a))).conj (map f x γ) :=
      (FundamentalGroupoid.map f).map_conj _ γ
    _ = _ := by
      rw [map_pathIso, fundamentalGroupMulEquivOfPath]
      rfl

end FundamentalGroup
end
