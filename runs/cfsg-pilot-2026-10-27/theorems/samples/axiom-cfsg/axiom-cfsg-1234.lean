public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs183eqv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)

section Cases

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_diag_of_moves {p : ℕ} (hp : p.Prime) {𝓛 : Set (Subgroup Y)} {b : Y}
    (hb : orderOf b = p) (hbN : b ∈ Subgroup.normalizer ((sSup 𝓛 : Subgroup Y) : Set Y))
    (hcomp : ∀ X ∈ 𝓛, IsComponentOf X ⊤)
    (hnot : ∀ X ∈ 𝓛, b ∉ Subgroup.normalizer (X : Set Y))
    {R : Subgroup Y} (hR : GLAPComponent p (sSup 𝓛 ⊓ Subgroup.centralizer ({b} : Set Y)) R) :
    ∃ X ∈ 𝓛, ∃ hc : (∀ j k, j < p → k < p → j ≠ k → ∀ x ∈ Input183.orbA b X j,
      ∀ y ∈ Input183.orbA b X k, x * y = y * x), R = (diagSub b p X hc).range := by
  classical
  set L : Subgroup Y := sSup 𝓛 with hL
  have hp0 : 0 < p := hp.pos
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  have hcomm : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x :=
    fun X hX X' hX' hne x hx y hy =>
      Prop95Parts.Input18.comp_comm (hcomp X hX) (hcomp X' hX') hne hx hy
  have hcompL : ∀ X ∈ 𝓛, IsComponentOf X L := fun X hX => l119_isComponentOf_sSup hcomp hcomm hX
  have hmem : ∀ X ∈ 𝓛, ∀ j : ℕ, Input183.orbA b X j ∈ 𝓛 := fun X hX j =>
    Input183.orbA_mem_family hL hcompL hcomm hbN hX j
  have hAcomm_of : ∀ X ∈ 𝓛, ∀ j k : ℕ, j < p → k < p → j ≠ k → ∀ x ∈ Input183.orbA b X j,
      ∀ y ∈ Input183.orbA b X k, x * y = y * x := fun X hX j k hj hk hjk x hx y hy =>
    hcomm _ (hmem X hX j) _ (hmem X hX k)
      (Input183.orbA_ne_of_not_normalizer hp hb (hnot X hX) hj hk hjk) x hx y hy
  have hAL : ∀ X ∈ 𝓛, ∀ j < p, Input183.orbA b X j ≤ L := fun X hX j _ => le_sSup (hmem X hX j)
  let Dg : Subgroup Y → Subgroup Y := fun X =>
    if h : X ∈ 𝓛 then (diagSub b p X (hAcomm_of X h)).range else ⊥
  have hDg : ∀ X (hX : X ∈ 𝓛), Dg X = (diagSub b p X (hAcomm_of X hX)).range :=
    fun X hX => dif_pos hX
  have hdiag_fixed : ∀ X (hX : X ∈ 𝓛) (x : ↥X),
      b * diagSub b p X (hAcomm_of X hX) x * b⁻¹ = diagSub b p X (hAcomm_of X hX) x :=
    fun X hX x => Input183.diag_shift hb hp0 (hAcomm_of X hX) (x : Y) x.2
  have hDM : ∀ X ∈ 𝓛, Dg X ≤ L ⊓ Subgroup.centralizer ({b} : Set Y) := by
    intro X hX d hd
    rw [hDg X hX] at hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · rw [diagSub_apply]
      exact Input183.oprod_mem fun j hj => hAL X hX j hj (Input183.mem_orbA x.2)
    · exact (mul_inv_eq_iff_eq_mul.1 (hdiag_fixed X hX x)).symm
  have hDOJ : ∀ X ∈ 𝓛, Dg X ≤ Input183.OJ b X := by
    intro X hX d hd
    rw [hDg X hX] at hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
    rw [diagSub_apply]
    exact Input183.oprod_mem fun j _ => Input183.orbA_le_OJ b X j (Input183.mem_orbA x.2)
  have hSO : ∀ X ∈ 𝓛, ∀ o ∈ Input183.OJ b X, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set Y),
      b * o * b⁻¹ = o * z → o ∈ Dg X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) := by
    intro X hX o ho z hz h
    rw [Input183.OJ_eq_fin hb hp0] at ho
    obtain ⟨x, hxX, w, hw, rfl⟩ := Input183.orbit_fixed hp0 hb hL hcomm
      (fun j _ => hmem X hX j) (fun j hj => hAL X hX j hj) (hAcomm_of X hX) hbN ho hz h
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hw)
    rw [hDg X hX]
    exact MonoidHom.mem_range.2 ⟨⟨x, hxX⟩, rfl⟩
  have hDeq : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, Input183.OJ b X = Input183.OJ b X' →
      Dg X' ≤ Dg X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) := by
    intro X hX X' hX' h d hd
    have hdOJ := hDOJ X' hX' hd
    rw [← h] at hdOJ
    rw [hDg X' hX'] at hd
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
    have hfix : b * diagSub b p X' (hAcomm_of X' hX') x * b⁻¹ =
        diagSub b p X' (hAcomm_of X' hX') x * 1 := by
      rw [mul_one]
      exact hdiag_fixed X' hX' x
    exact hSO X hX _ hdOJ 1 (L ⊓ Subgroup.centralizer (L : Set Y)).one_mem hfix
  obtain ⟨hC1, hC2⟩ := Input183.core_gen_normal hbp hp0 hL hmem hcomm Dg hDM hDOJ hSO hDeq
  obtain ⟨X, hX, hRX⟩ := eq_of_gen hp Dg hDM inf_le_left hC1 hC2
    (fun X hX => ⟨diagSub b p X (hAcomm_of X hX), (hDg X hX).symm⟩)
    (fun X hX => (hcomp X hX).2.2) hR
  exact ⟨X, hX, hAcomm_of X hX, hRX.trans (hDg X hX)⟩

end Cases
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs183eqv
end
