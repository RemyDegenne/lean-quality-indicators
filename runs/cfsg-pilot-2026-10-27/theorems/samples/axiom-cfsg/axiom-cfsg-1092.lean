public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace Split92

theorem mem_Z_of_comm_R₀ {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {x : G}
    (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t) {y : G} (hyV : y ∈ Vt M (LB M Q B) B Z t)
    (hy : ∀ e ∈ Sec9R0 hc t x, ⁅e, y⁆ ∈ Z) : y ∈ Z := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hR₀R : Sec9R0 hc t x ≤ Rt M (LB M Q B) t := Sec9R0_le_Rt hc hxR
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  let U : Subgroup G :=
    { carrier := {v | v ∈ Vt M (LB M Q B) B Z t ∧ ∀ e ∈ Sec9R0 hc t x, ⁅e, v⁆ ∈ Z}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(Vt M (LB M Q B) B Z t).mul_mem ha hb, fun e he => ?_⟩
        have e1 : ⁅e, a * b⁆ = ⁅e, a⁆ * (a * ⁅e, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e1]
        exact Z.mul_mem (ha' e he) (hZn _ (hQM (hVQ ha)) _ (hb' e he))
      one_mem' := ⟨(Vt M (LB M Q B) B Z t).one_mem, fun e _ => by
        simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(Vt M (LB M Q B) B Z t).inv_mem ha, fun e he => ?_⟩
        have e1 : ⁅e, a⁻¹⁆ = a⁻¹ * ⁅e, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e1]
        have := hZn _ (M.inv_mem (hQM (hVQ ha))) _ (Z.inv_mem (ha' e he))
        simpa using this }
  have hZU : Z ≤ U := fun z hz => ⟨sec39_Z_le_Vt hz, fun e he => by
    have h1 := HS9.Rt_cent_Z91 hc t (hR₀R he) hz
    rw [commutatorElement_def, h1, mul_inv_cancel]
    exact Z.one_mem⟩
  have hUV : U ≤ Vt M (LB M Q B) B Z t := fun v hv => hv.1
  have hRU : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U := by
    rintro ρ hρ u ⟨hu, hu'⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρ) u).mp hu,
      fun e he => ?_⟩
    have he' : ρ⁻¹ * e * ρ⁻¹⁻¹ ∈ Sec9R0 hc t x :=
      Sec9R0_conj_mem hc ht ((Rt M (LB M Q B) t).inv_mem hρ) he
    have e1 : ⁅e, ρ * u * ρ⁻¹⁆ = ρ * ⁅ρ⁻¹ * e * ρ⁻¹⁻¹, u⁆ * ρ⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact hZn _ (hc.Rt_le_M t hρ) _ (hu' _ he')
  rcases HS9.sec9VtIrred91 hs hZU hUV hRU with h | h
  · have : y ∈ U := ⟨hyV, hy⟩
    rw [h] at this
    exact this
  · exfalso
    apply hxN
    refine Ctx.mem_CN.mpr ⟨hxR, fun v hv => ?_⟩
    have hvU : v ∈ U := by rw [h]; exact hv
    exact hvU.2 x (mem_Sec9R0 hc t hxR)

end Split92
end CFSG.RankThree.GF2n.Stroth80
end
