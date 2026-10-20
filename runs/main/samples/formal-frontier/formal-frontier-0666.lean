@[expose] public section

universe u v w x z

namespace TopRep

variable {k : Type u} [CommRing k] [TopologicalSpace k]
    {G : Type x} [Group G]
    (X : TopRep.{v} k G) (Y : TopRep.{w} k G)

@[simp] theorem discreteLinHom_ρ_apply
    [ContinuousSMul k (DiscreteLinHom k X Y)]
    (g : G) (f : discreteLinHom X Y) (a : X) :
    (discreteLinHomToLinearMap X Y ((discreteLinHom X Y).ρ g f)) a =
      Y.ρ g ((discreteLinHomToLinearMap X Y f) (X.ρ g⁻¹ a)) := by
  rfl

end TopRep
end
