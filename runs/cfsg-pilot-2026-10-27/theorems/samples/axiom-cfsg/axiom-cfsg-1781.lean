public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed

universe u

variable {G : Type u} [Group G] {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
  (X : Subgroup G) (hSX : (S : Subgroup G) ≤ X)

theorem subModelBase_eq :
    modelBase (subSylow S X hSX) (subCoordinates S e X hSX) = (modelBase S e).subgroupOf X :=
  sub_map_eq S e X hSX _

end CFSG.Wreathed.BrauerWong
end
