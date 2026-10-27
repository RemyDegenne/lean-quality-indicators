public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

open scoped Pointwise commutatorElement

section Abstract

variable {G : Type} [Group G]

theorem m11AutInv_commutator (V : Subgroup G) : m11AutInv V ⁅V, V⁆ := by
  have key : Subgroup.map V.subtype ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ = ⁅V, V⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  intro α v hv
  rw [← key] at hv ⊢
  obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.mp hv
  have huv' : u = v := Subtype.ext huv
  rw [huv'] at hu
  refine Subgroup.mem_map.mpr ⟨α v, ?_, rfl⟩
  have h1 : Subgroup.map α.toMonoidHom ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ =
      ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ α.surjective]
  rw [← h1]
  exact Subgroup.mem_map.mpr ⟨v, hu, rfl⟩

end Abstract
end CFSG.OddStandard.SmallF3.HarrisU33.S4A
end
