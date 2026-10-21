namespace OAI

namespace PlanarFPP

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_ball_travel (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ a : Vertex,
      P.real {ω | ¬BallTravel μ D η δ s (fun e => τ (shiftEdge a e) ω)} < ε := by
  let _ := h.probability
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((exponential_ball_travel_nat h μ hμ ht D (η/2) (δ/2) hD (by linarith) (by linarith)).eventually
      (gt_mem_nhds hε))
  filter_upwards [eventually_ge_atTop (max 1 (N : ℝ))] with s hs
  intro a
  have he := translated_event_probability h a
    {w | ¬BallTravel μ D η δ s w} (measurableSet_ballTravel μ D η δ s).compl
  rw [show P.real {ω | ¬BallTravel μ D η δ s (fun e => τ (shiftEdge a e) ω)} =
      P.real {ω | ¬BallTravel μ D η δ s (fun e => τ e ω)} from congrArg ENNReal.toReal he]
  let n : ℕ := ⌈s⌉₊
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hsn : s ≤ (n : ℝ) := Nat.le_ceil s
  have hnN : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans hs).trans hsn
  have hnupper : (n : ℝ) ≤ 2*s := by
    have hh : (n : ℝ) < s+1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hη' : (η/2)*(n : ℝ) ≤ η*s := by nlinarith
  have hδ' : (δ/2)*(n : ℝ) ≤ δ*s := by nlinarith
  refine (measureReal_mono (show {ω | ¬BallTravel μ D η δ s (fun e => τ e ω)} ⊆
      {ω | ¬BallTravel μ D (η/2) (δ/2) n (fun e => τ e ω)} from ?_)).trans_lt (hN n hnN)
  intro ω hb hg
  apply hb
  intro p q hp hq
  apply localTravel_mono μ _ p q hη' hδ'
  apply hg p q <;> nlinarith

end PlanarFPP
end OAI
