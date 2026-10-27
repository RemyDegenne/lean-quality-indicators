public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

open CFSG.ASVolI.ChF

theorem burnsideF4n_inv_of_hasCycle1 {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) {a : α.G1} {u v : c.Γ}
    (h : HasCycle c (f1 (c := c) a) u v) (hu : u = c.lv) : a * a = 1 ∧ a ∉ α.α1.range := by
  obtain ⟨hss, hne, hsu, -⟩ := h
  refine ⟨f1_injective c hc (by rw [map_mul, hss, map_one]), fun ha => ?_⟩
  have := (burnsideF4n_f1_smul_lv_iff c hc a).mpr ha
  subst hu
  exact hne (this.symm.trans hsu)

end CFSG.ASVolI
end
