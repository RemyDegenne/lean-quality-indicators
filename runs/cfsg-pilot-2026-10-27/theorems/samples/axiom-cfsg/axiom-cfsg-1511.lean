public section

universe u

namespace CFSG.RankThree.S4Free.Stell

open Subgroup CFSG.Blueprint Suzuki

theorem exists_isL24_or_isL24Sz_of_nonsolvable
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) {H : Type*} [Group H]
    [Finite H] {S M A : Subgroup H}
    (hSz : ∀ E : Subgroup H, IsSimpleGroup E → (∃ x y : E, x * y ≠ y * x) →
      ∃ a : ℕ, 1 ≤ a ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * a + 1) ∧
        Nonempty (↥E ≃* suzukiGroup a K))
    (h : Hyp24 S M A) (hO : oTwo H = ⊥) (hD : M.normalCore = ⊥) (N : Subgroup H)
    (hNn : N.Normal) (hN1 : N ≠ ⊥) (hmin : ∀ K : Subgroup H, K.Normal → K ≤ N → K = ⊥ ∨ K = N)
    (hNs : ¬ Group.IsSolvable N) : ∃ L, IsL24 S M A L ∨ IsL24Sz S M A L := by
  obtain ⟨r, E, -, hEN, hEs, hconj, hEnorm, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNn hN1 hmin
  set C : Comps N r E := ⟨e, he, hEN⟩ with hCdef
  have hnin : ∀ k, ∀ n ∈ N, ∀ x ∈ E k, n * x * n⁻¹ ∈ E k := by
    intro k n hn x hx
    have := (hEnorm k).conj_mem ⟨x, hEN k hx⟩ hx ⟨n, hn⟩
    exact this
  have hconj' : ∀ i j, ∃ g : H, E j = (E i).map (MulAut.conj g).toMonoidHom := by
    intro i j
    obtain ⟨g, hg⟩ := hconj i j
    exact ⟨g⁻¹, hg⟩
  have hEna : ∀ i, ∃ x y : E i, x * y ≠ y * x := by
    intro i
    by_contra hcon
    push Not at hcon
    apply hNs
    have hcomm : ∀ j (x y : H), x ∈ E j → y ∈ E j → x * y = y * x := by
      intro j x y hx hy
      obtain ⟨g, hg⟩ := hconj' i j
      rw [hg] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      have := congrArg Subtype.val (hcon ⟨x', hx'⟩ ⟨y', hy'⟩)
      simp only [Subgroup.coe_mul] at this
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * x' * g⁻¹ * (g * y' * g⁻¹) = g * (x' * y') * g⁻¹ := by group
        _ = g * (y' * x') * g⁻¹ := by rw [this]
        _ = g * y' * g⁻¹ * (g * x' * g⁻¹) := by group
    have : ∀ n m : N, n * m = m * n := fun n m => C.ext_coord fun j => Subtype.ext (by
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm j _ _ (C.coord j n).2 (C.coord j m).2)
    exact isSolvable_of_comm this
  set Q : SzConfig S M A N r E :=
    SzConfig.mk C h hO hD hNn hEs (fun i => hSz _ (hEs i) (hEna i)) hnin hconj' hN1 with hQdef
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ¬ A ≤ centralizer (E i₀ : Set H) := by
    by_contra hcon
    push Not at hcon
    apply h.not_le_normalCore
    have hNA : N ≤ centralizer (A : Set H) :=
      Q.le_of_forall_le fun i => le_centralizer_iff.mp (hcon i)
    intro a ha
    rw [mem_normalCore_iff]
    intro g
    have hg : g ∈ ((M ⊔ N : Subgroup H) : Set H) := by rw [Q.sup_eq_top]; exact mem_top g
    rw [mul_normal] at hg
    obtain ⟨m, hm, n, hn, rfl⟩ := hg
    have hna : n * a = a * n := ((mem_centralizer_iff.mp (hNA hn)) a ha).symm
    rw [show m * n * a * (m * n)⁻¹ = m * (n * a * n⁻¹) * m⁻¹ by group, hna, mul_inv_cancel_right]
    exact M.mul_mem (M.mul_mem hm (h.le_M (h.le_S ha))) (M.inv_mem hm)
  set N₀ : Subgroup H := A ⊓ normalizer ((E i₀ : Subgroup H) : Set H) with hN₀def
  have hN₀iff : ∀ c, c ∈ N₀ ↔ c ∈ A ∧ (E i₀).map (MulAut.conj c).toMonoidHom = E i₀ := fun c => by
    rw [hN₀def, mem_inf, mem_normalizer_iff_map_conj_eq]
  by_cases hcase : ∃ n ∈ A, (E i₀).map (MulAut.conj n).toMonoidHom = E i₀ ∧
      ∃ w ∈ E i₀, n * w * n⁻¹ ≠ w
  ·
    obtain ⟨A₁, hA₁A, hA₁N₀, hdec⟩ :=
      exists_compl_of_isElemAbelian h.elemAb (inf_le_left : N₀ ≤ A)
    refine Q.exists_of_compl hSub i₀ hA₁A ?_ ?_ hcase
    · intro b hb
      obtain ⟨c, hc, n, hn, rfl⟩ := hdec b hb
      exact ⟨c, hc, n, ((hN₀iff n).mp hn).1, ((hN₀iff n).mp hn).2, rfl⟩
    · intro c hc hcE
      have : c ∈ A₁ ⊓ N₀ := ⟨hc, (hN₀iff c).mpr ⟨hA₁A hc, hcE⟩⟩
      rw [hA₁N₀] at this
      exact mem_bot.mp this
  ·
    push Not at hcase
    obtain ⟨a, haA, haN⟩ : ∃ a ∈ A, a ∉ N₀ := by
      by_contra hcon
      push Not at hcon
      apply hi₀
      intro b hb
      rw [mem_centralizer_iff]
      intro w hw
      have := hcase b hb ((hN₀iff b).mp (hcon b hb)).2 w hw
      calc w * b = b * w * b⁻¹ * b := by rw [this]
        _ = b * w := by group
    obtain ⟨A₁, hN₀A₁, hA₁A, haA₁, hidx⟩ :=
      exists_hyperplane_of_isElemAbelian h.elemAb inf_le_left haA haN
    exact (Q.exists_isL24_of_hyperplane i₀ hA₁A hidx haA haA₁
      (fun c hc hcE => hN₀A₁ ((hN₀iff c).mpr ⟨hc, hcE⟩)) hcase).imp fun L hL => Or.inl hL

end CFSG.RankThree.S4Free.Stell
end
