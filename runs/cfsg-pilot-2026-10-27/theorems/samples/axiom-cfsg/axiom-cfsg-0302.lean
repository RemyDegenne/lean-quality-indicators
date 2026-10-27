public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint

open CFSG.GH74.E2 hiding Hyp

theorem noPairU33_of_inner (hD3 : K0Data3) (hS : SmallData ShapeU33)
    {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (hcfg : Cfg G T z L) (hsh : ShapeU33 ↥L) (hinn : InnerAction (T : Subgroup G) L) : False := by
  have hZ : center ↥L = ⊥ :=
    hD3.center_bot ↥L (Or.inr (Or.inl hsh))
  obtain ⟨U, hU, hr⟩ := hD3.rank_ge3 ↥L (Or.inr (Or.inl hsh))
  exact hcfg.false_of_smallTable hZ hinn (hcfg.tC_cyclic hZ hU hr) (hcfg.smallTable hS hsh)

end CFSG.GH74.AS16.E2
end
