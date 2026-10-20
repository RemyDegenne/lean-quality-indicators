public section

open MeasureTheory Set Filter Topology

open CKN

noncomputable section

namespace CIV

theorem excess_eq_add_intervalIntegral {m d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ} {q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε)
    (M σ K : ℝ) (x : Vec m)
    (hCont : ContinuousOn (fun τ => mollifySlice m ε q (x, τ)) I)
    (hLoc : LocallyIntegrableOn (fun τ => partialLaplacian m d (mollifySlice m ε q) (x, τ)
        - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
        + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
            (fun y => q (y, τ)) x) I volume)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I) {τ : ℝ} (hτ : τ ∈ I) :
    (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ))
      = (mollifySlice m ε q (x, τ₀) - barrier m M σ K τ₀ (x, τ₀))
        + ∫ s in τ₀..τ, ((partialLaplacian m d (mollifySlice m ε q) (x, s)
            - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
            + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
                (fun y => q (y, s)) x) - σ * K) := by
  have hM := mollifySlice_eq_add_intervalIntegral hI hIoc hB hq heq hε x hCont hLoc hτ₀ hτ
  have hUIcc : uIcc τ₀ τ ⊆ I := hIoc.uIcc_subset hτ₀ hτ
  have hhIcc : IntegrableOn (fun τ => partialLaplacian m d (mollifySlice m ε q) (x, τ)
      - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
      + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
          (fun y => q (y, τ)) x) (uIcc τ₀ τ) volume :=
    hLoc.integrableOn_compact_subset hUIcc isCompact_uIcc
  have hhInterval : IntervalIntegrable (fun τ => partialLaplacian m d (mollifySlice m ε q) (x, τ)
      - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
      + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
          (fun y => q (y, τ)) x) volume τ₀ τ :=
    intervalIntegrable_iff.mpr (hhIcc.mono_set uIoc_subset_uIcc)
  have hconstInterval : IntervalIntegrable (fun _ : ℝ => σ * K) volume τ₀ τ :=
    intervalIntegrable_const
  have hBar : barrier m M σ K τ₀ (x, τ) - barrier m M σ K τ₀ (x, τ₀) = ∫ s in τ₀..τ, σ * K := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    unfold barrier
    ring
  have hsplit : (∫ s in τ₀..τ, ((partialLaplacian m d (mollifySlice m ε q) (x, s)
      - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
      + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
          (fun y => q (y, s)) x) - σ * K))
      = (∫ s in τ₀..τ, (partialLaplacian m d (mollifySlice m ε q) (x, s)
          - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
          + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
              (fun y => q (y, s)) x))
        - ∫ s in τ₀..τ, σ * K :=
    intervalIntegral.integral_sub hhInterval hconstInterval
  rw [hsplit, ← hBar]
  linarith only [hM]

end CIV
end
end
