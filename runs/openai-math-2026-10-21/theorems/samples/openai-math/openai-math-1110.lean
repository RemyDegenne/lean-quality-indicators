namespace OAI

section

namespace MaximalSeshadri.Interpolation

open scoped BigOperators Pointwise

open scoped BigOperators ContDiff

open Filter Topology

open scoped BigOperators Topology

open Filter Set

theorem initial_monomial_jet_transfer (V : Submodule ℂ (Exponent → ℂ))
    [FiniteDimensional ℂ V] (hc : ∀ c ∈ V, ConvergentSeries c)
    (t : ℝ) (ht : 0 < t) (r m : ℕ) (p : Fin r → ℂ × ℂ)
    (hp : Function.Injective p)
    (hjet : LinearIndependent ℂ (fun e : initialExponentSet V t =>
      finiteJetColumn r m p (fun x z => x ^ e.val.1 * z ^ e.val.2))) :
    ∃ R : ℝ, 0 < R ∧ (∀ c ∈ V, DerivativeSummable c R) ∧
      ∀ ε : ℝ, 0 < ε → ∃ q : Fin r → ℂ × ℂ, Function.Injective q ∧
        (∀ j, ‖(q j).1‖ < min ε R ∧ ‖(q j).2‖ < min ε R) ∧
        Function.Injective (fun f : V => finiteJetColumn r m q (seriesEval f)) := by
  classical
  obtain ⟨hE, b, hb⟩ := exists_initial_basis V t ht
  have := hE.to_subtype
  have hc' (e : initialExponentSet V t) : ConvergentSeries (b e : Exponent → ℂ) :=
    hc _ (b e).property
  obtain ⟨u, htu, hu⟩ := exists_strictWeight_of_lex
    (fun e => (b e : Exponent → ℂ)) (fun e => e.val) t ht hb
  obtain ⟨R, hR, hDR⟩ := exists_commonDerivativeRadius V hc
  refine ⟨R, hR, hDR, ?_⟩
  intro ε hε
  obtain ⟨q, hqi, hqn, hqj⟩ := initial_monomial_jet_transfer_strict
    (fun e => (b e : Exponent → ℂ)) (fun e => e.val) u (ht.trans htu) hu hc'
    r m p hp hjet (min ε R) (lt_min hε hR)
  have hqR (j) : ‖(q j).1‖ < R ∧ ‖(q j).2‖ < R :=
    ⟨(hqn j).1.trans_le (min_le_right _ _), (hqn j).2.trans_le (min_le_right _ _)⟩
  refine ⟨q, hqi, hqn, ?_⟩
  have hjli : LinearIndependent ℂ (seriesJetMap V R hDR r m q hqR ∘ b) := by
    simpa only [Function.comp_def, seriesJetMap_eq] using hqj
  have hinj := LinearMap.injective_of_linearIndependent b.span_eq hjli
  intro f g hfg
  apply hinj
  simpa only [seriesJetMap_eq] using hfg

end MaximalSeshadri.Interpolation
end
end OAI
