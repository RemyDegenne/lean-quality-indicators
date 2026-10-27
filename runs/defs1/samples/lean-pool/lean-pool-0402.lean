universe v w

open scoped HahnSeries NatOrdinal Topology

open Filter Berarducci HahnSeries MvPolynomial

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]

variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

variable {σ : Lifts wt x} {α : NatOrdinal}

namespace Lifts

namespace RealPartialDecomposition

variable (S : HahnSeries.Germ.LimitOrdinalRelationAtCutoff σ.cantorBendixson α)

/-- A generic relation of limit-ordinal degree reinterpreted in the real principal subring. -/
@[expose] def principal : σ.LimitOrdinalRelationAtCutoff α := by
  let hex := eventually_nhdsLT_iff_exists.mp S.truncation_lt
  let l := Classical.choose hex
  have hl := (Classical.choose_spec hex).1
  have htrunc := (Classical.choose_spec hex).2
  refine
    { F := S.F
      hom := S.hom
      eval_zero := ?_
      ne_zero := S.ne_zero
      vars_lt := S.vars_lt
      vars_limit := S.vars_limit
      B₀ := S.B₀
      mem := S.mem
      max := S.max
      β := S.β
      degHD := S.degHD
      hdegHD := S.hdegHD
      degHD_terms := S.degHD_terms
      degHD_ne_zero := S.degHD_ne_zero
      term_lt := S.term_lt
      lam₀ := S.lam₀
      lam₀_lt := S.lam₀_lt
      α₁ := S.α₁
      α₁_le := S.α₁_le
      α₁_le_α := S.α₁_le_α
      ε₁ := -l
      ε₁_pos := neg_pos.mpr hl
      truncation_lt := ?_
      remainder_lt := S.remainder_lt }
  · apply principalSubringCantorBendixsonAlgEquiv.injective
    rw [map_zero, principalSubringCantorBendixsonAlgEquiv_aeval, S.eval_zero]
  · intro γ hγl hγ0
    apply (ordinalValueDegree_lt_coe_iff _ _).mp
    rw [show -l = -l by rfl] at hγl
    have hcb := htrunc γ (by linarith) hγ0
    rw [show σ.cantorBendixson.lift = σ.lift by
      funext i
      exact cantorBendixson_lift σ i] at hcb
    rw [ordinalValueDegree_eq_cantorBendixsonDegree]
    simpa only [translatedTruncLE_eq_translatedTruncation] using hcb

end RealPartialDecomposition
end Lifts
end Berarducci
end
