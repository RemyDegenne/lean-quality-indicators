public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Item116Fusion

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem exists_mem_closure_mul_pow (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) {x : G} (hx : x ∈ A) :
    ∃ b ∈ Subgroup.closure ({c, d} : Set G), ∃ k : ℕ, k < 3 ∧ x = b * a ^ k := by
  obtain ⟨f, -, -, -, hfv⟩ := exists_coords_cda h hdL hdc
  set v := Multiplicative.toAdd (f.symm ⟨x, hx⟩) with hv
  have hx' : x = (f (Multiplicative.ofAdd v) : G) := by
    rw [hv, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  rw [hfv] at hx'
  refine ⟨c ^ (v 0).val * d ^ (v 1).val, Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _), (v 2).val, ZMod.val_lt _, hx'⟩

end Certified
end Item116Fusion
end CFSG.RankThree.PartTwo.Sec11
end
