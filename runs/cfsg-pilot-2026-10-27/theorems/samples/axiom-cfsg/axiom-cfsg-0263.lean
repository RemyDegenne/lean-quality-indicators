public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_z3_exists_xbar_of_bar {D : Data G} {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) {p n : ℕ}
    {X : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))}
    (hXn : ∀ q ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian, ∀ x ∈ X, q * x * q⁻¹ ∈ X)
    (hXe : IsElemAbelian p X)
    (hXd : X ≤ ⁅Mbar D.M V₀ V h.hyp125.isElemAbelian, Mbar D.M V₀ V h.hyp125.isElemAbelian⁆)
    (hcard : Nat.card ↥X = p ^ n) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    ∃ Xbar : Subgroup (F11.MBar11 D.M V₀ V), Xbar.Normal ∧ IsElemAbelian p Xbar ∧
      Nat.card Xbar = p ^ n ∧ Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ ∧
      barSub V₀ V h.hyp125.isElemAbelian (F11.barPreimage11 D.M V₀ V Xbar) ≤ X := by
  let hV := h.hyp125.isElemAbelian
  have hXM : X ≤ Mbar D.M V₀ V hV := hXd.trans (Subgroup.commutator_le_self _)
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv hV hMs
  set Xbar : Subgroup (F11.MBar11 D.M V₀ V) :=
    (X.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom with hXbar
  have hNnorm : (X.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
    refine ⟨fun x hx q => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      hXn (q : MulAut (Vtil V₀ V hV)) q.2 (x : MulAut (Vtil V₀ V hV)) hx
  have hXnorm : Xbar.Normal := by
    rw [hXbar]
    exact hNnorm.map e.symm.toMonoidHom e.symm.surjective
  have hXab : IsElemAbelian p Xbar := by
    rw [hXbar]
    exact (hXe.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom
  have hcardX : Nat.card ↥Xbar = p ^ n := by
    rw [hXbar, Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, hcard]
  have hcomm_le : X.subgroupOf (Mbar D.M V₀ V hV) ≤
      (⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆).subgroupOf (Mbar D.M V₀ V hV) :=
    fun x hx => hXd (Subgroup.mem_subgroupOf.1 hx)
  have hcommmap : ((⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆).subgroupOf
        (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom =
      ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
    rw [s16h_z3_subgroupOf_commutator_self, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr e.symm.surjective]
  have hXcomm : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
    rw [hXbar]
    exact le_trans (Subgroup.map_mono hcomm_le) (le_of_eq hcommmap)
  have hXM' : F11.barPreimage11 D.M V₀ V Xbar ≤ D.M := by
    unfold F11.barPreimage11
    exact Subgroup.map_subtype_le _
  have himg : F11.barImage11 D.M V₀ V (F11.barPreimage11 D.M V₀ V Xbar) = Xbar :=
    s16h_z3_barImage11_barPreimage11 D Xbar
  have h2 : Xbar.map e.toMonoidHom = X.subgroupOf (Mbar D.M V₀ V hV) := by
    rw [hXbar, Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext x; simp
    rw [hcomp, Subgroup.map_id]
  refine ⟨Xbar, hXnorm, hXab, hcardX, hXcomm, ?_⟩
  intro φ hφ
  have hφM : φ ∈ Mbar D.M V₀ V hV := (barSub_mono V₀ V hV hXM') hφ
  have h1 := he (F11.barPreimage11 D.M V₀ V Xbar) hXM'
  rw [himg, h2] at h1
  have hmem : (⟨φ, hφM⟩ : ↥(Mbar D.M V₀ V hV)) ∈
      (barSub V₀ V hV (F11.barPreimage11 D.M V₀ V Xbar)).subgroupOf
        (Mbar D.M V₀ V hV) := hφ
  rw [← h1] at hmem
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
