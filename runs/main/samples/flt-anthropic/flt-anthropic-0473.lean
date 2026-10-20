namespace P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add

set_option maxHeartbeats 800000

set_option autoImplicit false

universe u

set_option autoImplicit false

set_option autoImplicit false

open Finset BigOperators

set_option autoImplicit false

p2m_open

namespace ModularCurve

namespace UVCrossingModel

p2m_open

open AnnulusNF AnnulusStepA

variable {W : Type u} [CommRing W]

section Scaled

variable [IsDomain W] [IsDiscreteValuationRing W]

theorem dominantIndices_finite_nonempty [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp1 : 1 ≤ p) (hpe : p + 1 ≤ q * e) :
    (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab).Finite ∧
      (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab).Nonempty := by
  change (dominantIndices (vq W q) (q * e) p ab).Finite ∧ (dominantIndices (vq W q) (q * e) p ab).Nonempty
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := habx ▸ hx
  have hfin := iInf_termOrder_lt_top (vq W q) (vq_eq_top q) (ϖ ^ e) (q * e) p ab hb hx'
  obtain ⟨lb, hlb⟩ := dominantIndices_bddBelow (vq W q) (vq_zero q hq) (q * e) p (by omega) ab hb hfin
  obtain ⟨ub, hub⟩ := dominantIndices_bddAbove (vq W q) (vq_zero q hq) (q * e) p (by omega) ab hb hfin
  exact ⟨(Set.finite_Icc lb ub).subset fun n hn => ⟨hlb hn, hub hn⟩,
    dominantIndices_nonempty _ (vq_zero q hq) _ p ab hb⟩

end Scaled
end UVCrossingModel
end ModularCurve
end P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add
