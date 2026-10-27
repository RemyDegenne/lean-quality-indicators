public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

theorem exists_sylow_dihedral_eight {M : Type*} [Group M] [Finite M] {Y : Subgroup M} {x y : M}
    (hxY : x ∈ Y) (hyY : y ∈ Y) (h4 : x ^ 4 = 1) (hord : orderOf x = 4) (hy : y * y = 1)
    (hrel : y * x * y⁻¹ = x⁻¹) (hnot : y ∉ zpowers x) (hfac : (Nat.card Y).factorization 2 = 3) :
    ∃ P : Sylow 2 ↥Y, Nonempty ((P : Subgroup ↥Y) ≃* DihedralGroup (2 ^ (3 - 1))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := HSFLit.injective_dihedralLift 4 x y h4 hy hrel hord hnot
  have hrange := HSFLit.range_dihedralLift 4 x y h4 hy hrel
  set D := zpowers x ⊔ zpowers y with hD
  have hDY : D ≤ Y := sup_le (zpowers_le.mpr hxY) (zpowers_le.mpr hyY)
  have hDcard : Nat.card D = 8 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, DihedralGroup.nat_card]
  have hcard : Nat.card (D.subgroupOf Y) = 2 ^ (Nat.card Y).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDY).toEquiv, hDcard, hfac]
    norm_num
  refine ⟨Sylow.ofCard _ hcard, ⟨?_⟩⟩
  exact (subgroupOfEquivOfLe hDY).trans
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm

end CFSG.ComponentClassification.GrSLit
end
