public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable (hst : S.Asc512Standing)

include hst

theorem asc_mk_injOn {d e : S.LbarAsc} (hd : (d : S.O) ∈ S.DbarAsc) (he : (e : S.O) ∈ S.DbarAsc)
    (h : (QuotientGroup.mk d : S.LbarAsc ⧸ center S.LbarAsc) = QuotientGroup.mk e) : d = e := by
  have hu : d⁻¹ * e ∈ center S.LbarAsc := QuotientGroup.eq.mp h
  have hd2 : d * d = 1 := Subtype.ext (asc_mul_self_of_mem hd)
  have he2 : e * e = 1 := Subtype.ext (asc_mul_self_of_mem he)
  have hde : d * e = e * d := by
    have h1 := mem_center_iff.1 hu d
    calc d * e = d * (d * (d⁻¹ * e)) * d⁻¹ * d := by group
      _ = d * ((d⁻¹ * e) * d) * d⁻¹ * d := by rw [h1]
      _ = e * d := by group
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hu2 : (d⁻¹ * e) * (d⁻¹ * e) = 1 := by
    rw [hdinv]
    calc d * e * (d * e) = d * (e * d) * e := by group
      _ = d * (d * e) * e := by rw [hde]
      _ = (d * d) * (e * e) := by group
      _ = 1 := by rw [hd2, he2, one_mul]
  have := asc_center_eq_one hst hu hu2
  calc d = d * (d⁻¹ * e) := by rw [this, mul_one]
    _ = e := by group

end Setting
end CFSG.LargeExtraspecial
end
