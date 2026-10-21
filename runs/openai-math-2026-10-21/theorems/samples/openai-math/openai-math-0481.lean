namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

theorem exists_unconditioned_rootBudget_absolute_family
    (s n₀ : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
    (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)]
    (B : ℝ) (hBP : unconditionedResidueSiteBound P ≤ B) (i : X)
    {p a Λ σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (d₀ : ℕ) (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hprime : ∀ k, (P k).Prime) (hdistinct : Function.Injective P)
    (hcomparable : ∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j)
    (hcutoff : ∀ k, Real.exp p ≤ (P k : ℝ))
    (N : X → ℕ)
    (hN : ∀ j, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := Fin n₀) B τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive,
        RelativePatchSliceConclusion s P
          (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) Λ d₀ p) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1,
        ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N := by
  let f₀ := fun x => if x ∈ integerBox N then f x else 0
  have hf₀ : ∀ x, f₀ x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    by_cases hx : x ∈ integerBox N
    · simpa only [f₀, ite_eq_left hx] using hf x hx
    · simp only [f₀, ite_eq_right hx, Set.mem_Icc, le_refl, zero_le_one, and_self]
  have hmean₀ : a + σ ≤ 𝔼 x ∈ integerBox N, f₀ x := by
    have he : (𝔼 x ∈ integerBox N, f₀ x) = 𝔼 x ∈ integerBox N, f x :=
      Finset.expect_congr rfl (fun x hx => ite_eq_left hx)
    rwa [he]
  obtain ⟨hW, hR, hZ, productive, hmass, hinj, hlocal, hinside⟩ :=
    exists_unconditioned_rootBudget_productive_family P B hBP i ha hσ hσ1 N hN f₀ hf₀ hmean₀
  refine ⟨hW, hR, hZ, productive, hmass, hinj, ?_, hinside⟩
  intro z hz
  have hlocal' : a ≤ 𝔼 u : ∀ k, ZMod (P k),
      f (jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val)) := by
    have h := hlocal z hz
    simp only [f₀, ite_eq_left (hinside z _)] at h
    linarith
  obtain ⟨hbound, hAP, hmean⟩ := unconditionedAbsoluteSample_input
    s N P (z.1.val,z.2.val) f hf hfree (hinj z hz) (hinside z) hlocal'
  exact habsolute P hprime hdistinct hcomparable hcutoff
    (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) hbound hAP hmean

end BooleanCubeKernel
end Erdos3
end
end OAI
