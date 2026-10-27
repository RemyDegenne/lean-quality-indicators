public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG

theorem r5a_eq_of_mk_eq {M : Type*} [Group M] (R : Subgroup M) [R.Normal] {F : Subgroup M}
    (hF : F ⊓ R = ⊥) {x y : M} (hx : x ∈ F) (hy : y ∈ F)
    (hxy : QuotientGroup.mk' R x = QuotientGroup.mk' R y) : x = y := by
  have h1 : x⁻¹ * y ∈ R := QuotientGroup.eq.mp hxy
  have h2 : x⁻¹ * y ∈ F ⊓ R := ⟨F.mul_mem (F.inv_mem hx) hy, h1⟩
  rw [hF, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.mp h2

end CFSG.RankThree.PartTwo.Sec13.F135Last
end
