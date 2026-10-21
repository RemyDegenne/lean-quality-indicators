namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_reduced_fast_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ReducedFastResetSpec s a C := by
  have hresetExists := exists_controlled_reduced_fast_reset s a
  obtain ⟨c, _, hreset⟩ := hresetExists
  let Q : Polynomial ℕ := 3 * (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) *
    (Polynomial.X + 1) + 2 * Polynomial.X + 2
  let B := (Q + Polynomial.C c) ^ c
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U v hspan hU H l p hH hl hp hι hσ hκ hHp hlp hc hv
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let q := reducedMatrixParameter s p
  have hq : 0 ≤ q := reducedMatrixParameter_nonneg s hp
  have hpq : p ≤ q := le_reducedMatrixParameter s hp
  have hdims := F.reduced_lift_matrix_dimensions e ω hF w hw hp hι hσ hκ
  have hfinal : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, Q, q, reducedMatrixParameter, Polynomial.eval₂_pow] using hbound p hp
  have hrawExists := hreset F e ω hF w hw U v hspan hU H l q hH hl hq
    hdims.1 (hσ.trans hpq) hdims.2.1 hdims.2.2 (hHp.trans (Real.exp_le_exp.mpr hpq))
    (hlp.trans (Real.exp_le_exp.mpr hpq)) hc hv
  obtain ⟨S, m, hm, hmp, hlm, hraw⟩ := hrawExists
  refine ⟨S, m, hm, hmp.trans (Real.exp_le_exp.mpr hfinal), hlm, ?_⟩
  intro T hT E P R A D hP hleft hright hE hR hLeftSlow hRightRat
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp ((q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a)
  have hE' := F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hT hinput E hE
  have hLeftSlow' := F.quotientTop.symbolSlowBound_mono (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T hT hinput _ hLeftSlow
  have hresult := hraw T hT E P R A D hP hleft hright hE' hR hLeftSlow' hRightRat
  obtain ⟨hprod, hfast, hA, hD, hmid, hslow, hgrid⟩ := hresult
  refine ⟨hprod, hfast, hA, hD, hmid, ?_, hgrid⟩
  exact F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hT
    (Real.exp_le_exp.mpr hfinal) _ hslow

end Erdos3.NilpotentLieFiltration
end
end OAI
