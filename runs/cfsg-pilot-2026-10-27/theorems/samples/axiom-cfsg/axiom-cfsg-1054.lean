public section

namespace CFSG.RankThree.GF2n.Tim79.QuadModel

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem finrank_range_eq_two_and_singular_of_flag [CharP K 2] (M₀ : QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e)
    {W : Submodule K M₀.E} (hWs : ∀ w ∈ W, M₀.Qf w = 0)
    (hWo : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) (hW3 : Module.finrank K W = 3)
    {b : M₀.E} (hb : b ≠ 0) (hbW : b ∈ W) (hTb : T b = b)
    (hTW : ∀ w ∈ W, ∃ c : K, T w - w = c • b) (hT1 : ∃ v, T v ≠ v)
    {S : M₀.E →ₗ[K] M₀.E} (hS : ∀ e, M₀.Qf (S e) = M₀.Qf e) (hST : ∀ e, S (T e) = T (S e))
    (hSb : ∀ c : K, S b ≠ c • b) :
    Module.finrank K (LinearMap.range (T - 1)) = 2 ∧
      ∀ v ∈ LinearMap.range (T - 1), M₀.Qf v = 0 := by
  obtain ⟨hP, hdisj⟩ :=
    finrank_range_sub_one_le_two_of_flag M₀ hT hT2 hWs hWo hW3 hb hbW hTb hTW
  have hQb : M₀.Qf b = 0 := hWs b hbW
  rcases hdisj with hleW | hbR
  · have hs : ∀ v ∈ LinearMap.range (T - 1), M₀.Qf v = 0 :=
      fun v hv => hWs v (hleW hv)
    have h2 := two_le_finrank_range_sub_one M₀ hT hT1 hs
    exact ⟨le_antisymm hP h2, hs⟩
  · obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hbR
    have hv' : T v - v = b := by
      simpa only [LinearMap.sub_apply, Module.End.one_apply] using hv
    have hSbP : S b ∈ LinearMap.range (T - 1) := by
      refine ⟨S v, ?_⟩
      show T (S v) - S v = S b
      rw [← hST v, ← map_sub, hv']
    have hQb' : M₀.Qf (S b) = 0 := by rw [hS b, hQb]
    have hB : M₀.B b (S b) = 0 := by
      have h1 : M₀.B b (S b) = M₀.B (T v - v) (S b) := by rw [hv']
      rw [h1, B_sub_self_adjoint M₀ hT hT2 v (S b)]
      have h0 : T (S b) = S b := by rw [← hST b, hTb]
      rw [h0, sub_self, map_zero]
    exact finrank_range_eq_two_of_mem M₀ hP hbR hSbP hb hSb hQb hQb' hB

end CFSG.RankThree.GF2n.Tim79.QuadModel
end
