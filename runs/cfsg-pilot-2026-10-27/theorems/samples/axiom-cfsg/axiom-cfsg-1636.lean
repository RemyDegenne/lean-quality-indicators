public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap

open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec9_notQB (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) : ¬ Vt M (LB M Q B) B Z t ≤ QB B := by
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV := hc.B_le_Vt hs5.mem
  have hVQ := hc.Vt_le_Q t
  obtain ⟨K, _, _, hK, φ, hφr, -, hsec⟩ := hs.plus4
  refine hc.not_le_QB_of_natural h35 hLR hZV hBV hVQ hK (ι := Fin 2 ⊕ Fin 2) ?_ φ hsec
    (polarBilin (quadPlus 2 K)) ?_
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rintro A ⟨s, rfl⟩ u hu hrank
    have hA : φ s ∈ StatedOmega (StatedQuadPlus 2 K) := by
      rw [← hφr]
      exact ⟨s, rfl⟩
    exact omega_hform (coe_quadPlus 2 K) (nondegenerate_polarBilin_quadPlus 2 K) hA hu hrank

end CFSG.RankThree.GF2n.Stroth80
end
