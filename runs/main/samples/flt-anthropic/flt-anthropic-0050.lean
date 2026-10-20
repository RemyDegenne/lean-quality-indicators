namespace P2MW.S_ModularCurve_toricPoint_add_toricPoint_of_charZero

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option autoImplicit false

noncomputable section

p2m_open

open scoped Topology Uniformity

namespace HahnSeries

namespace XAdicRatToric

p2m_open

variable (K : Type*) [Field K]

scoped instance valued : Valued (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ) :=
  Valued.mk' (AddValuation.toValuation (HahnSeries.addVal ℚ K))

scoped instance mulArchimedean : MulArchimedean (Multiplicative (WithTop ℚ)ᵒᵈ) where
  arch x y hy := by
    have hg : OrderDual.ofDual (Multiplicative.toAdd y) < (0 : WithTop ℚ) := hy
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp (hg.ne_top)
    rw [← hq] at hg
    have hq0 : q < 0 := by exact_mod_cast hg
    rcases eq_or_ne (OrderDual.ofDual (Multiplicative.toAdd x)) ⊤ with hx | hx
    · refine ⟨0, ?_⟩
      rw [pow_zero]
      change (0 : WithTop ℚ) ≤ OrderDual.ofDual (Multiplicative.toAdd x)
      exact hx ▸ le_top
    · obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hx
      obtain ⟨n, hn⟩ := Archimedean.arch (-p) (neg_pos.mpr hq0)
      refine ⟨n, ?_⟩
      change (n • OrderDual.ofDual (Multiplicative.toAdd y) : WithTop ℚ)
        ≤ OrderDual.ofDual (Multiplicative.toAdd x)
      rw [← hq, ← hp, ← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul]
      rw [nsmul_eq_mul] at hn; linarith

scoped instance isNontrivial :
    (Valued.v : Valuation (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ)).IsNontrivial := by
  refine ⟨⟨single (1 : ℚ) (1 : K), (Valuation.ne_zero_iff _).mpr (single_ne_zero' K 1), ?_⟩⟩
  intro h
  have h1 : (0 : WithTop ℚ) < (single (1 : ℚ) (1 : K)).orderTop := by
    rw [orderTop_single one_ne_zero]; exact_mod_cast one_pos
  have := (valued_lt_one_iff K _).mpr h1
  rw [h] at this
  exact lt_irrefl _ this

scoped instance rankOne :
    (Valued.v : Valuation (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ)).RankOne :=
  (nonempty_rankOne K).some

scoped instance nontriviallyNormedField : NontriviallyNormedField (HahnSeries ℚ K) :=
  Valued.toNontriviallyNormedField (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ)

scoped instance isUltrametricDist : IsUltrametricDist (HahnSeries ℚ K) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (Valued.isNonarchimedean_norm (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ))

scoped instance (priority := low) decidableEq : DecidableEq (HahnSeries ℚ K) := Classical.decEq _

variable {K}

variable (K)

theorem gamma0_ne_zero_iff (a : Multiplicative (WithTop ℚ)ᵒᵈ) :
    a ≠ 0 ↔ OrderDual.ofDual (Multiplicative.toAdd a) ≠ (⊤ : WithTop ℚ) :=
  ⟨fun ha h ↦ ha (Multiplicative.toAdd.injective (OrderDual.ofDual.injective h)),
   fun h ha ↦ h (ha ▸ rfl)⟩

end XAdicRatToric
end HahnSeries
end
end P2MW.S_ModularCurve_toricPoint_add_toricPoint_of_charZero
