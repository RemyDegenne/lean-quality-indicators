public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.SzR1.Vert

open scoped commutatorElement

namespace VertT

variable {G : Type*} [Group G] {P S Q W Z M : Subgroup G}

theorem relIndex_conjSub (g : G) {A B : Subgroup G} :
    (conjSub g A).relIndex (conjSub g B) = A.relIndex B := by
  unfold conjSub
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulEquiv.injective _)

end VertT
end CFSG.Quasithin.Background.Harris.R1
end
