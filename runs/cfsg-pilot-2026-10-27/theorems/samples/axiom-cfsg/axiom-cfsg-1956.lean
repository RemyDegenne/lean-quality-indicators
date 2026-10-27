public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W] {G X Y : Subgroup (MulAut W)}

variable [Finite W]

theorem comm_of_fixes_commSub (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X)
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hfix : ∀ y ∈ Y, ∀ u ∈ commSub (⊤ : Subgroup W) X, y u = u) :
    ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  intro x hx y hy
  ext v
  have hv : v ∈ fixV X ⊔ commSub ⊤ X := by
    rw [fixV_sup_commSub_eq_top' hW hX.2.2.2.1]
    exact Subgroup.mem_top v
  obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup.1 hv
  have hyc : y c ∈ fixV X := fixV_stable_of_normalizer (hYN hy) hc
  have hxu : x u ∈ commSub (⊤ : Subgroup W) X := commSub_stable' hx hu
  simp only [MulAut.mul_apply, map_mul]
  rw [hyc x hx, hc x hx, hfix y hy u hu, hfix y hy _ hxu]

end Pf
end Asc81c
end CFSG.Quasithin
end
