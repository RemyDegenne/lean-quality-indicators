public section

noncomputable section

open CategoryTheory TauCeti

open scoped unitInterval Topology Topology.Homotopy

universe u

namespace HomotopyGroup

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
  (R : Type u) [Ring R] (n : ℕ)

theorem cubicalHurewicz_map (f : C(X, Y)) (hf : f x = y) (a : HomotopyGroup (Fin (n + 1)) X x) :
    cubicalHurewicz R n (HomotopyGroup.map f hf a) =
      HomologicalComplex.homologyMap ((normalizedCubicalChainComplex R).map (TopCat.ofHom f))
        (n + 1) (cubicalHurewicz R n a) :=
  Quotient.inductionOn a (GenLoop.cubicalHurewicz_map R f hf)

end HomotopyGroup
end
end
