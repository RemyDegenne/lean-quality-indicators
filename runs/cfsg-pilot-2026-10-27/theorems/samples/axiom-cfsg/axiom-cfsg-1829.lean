public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType

open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G]

variable [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem l24_ker_iff {X Y : Subgroup G} {β : ↥X →* Multiplicative (Fin 2 → F4)}
    (hβk : β.ker = Y.subgroupOf X) (x : ↥X) :
    β x = 1 ↔ (x : G) ∈ Y := by
  rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]

end CFSG.Quasithin.H13.L32A
end
