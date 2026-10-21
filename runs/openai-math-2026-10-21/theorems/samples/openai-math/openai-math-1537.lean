namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

open FiniteProbabilityWeights

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance badProductSmoothIndexFintype (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedSmoothRankCoefficientIndex X inactive L) := inferInstance

noncomputable local instance badProductDeckIndexFintype :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance

noncomputable local instance badProductDeckIndexDecidableEq :
    DecidableEq (AllocatedDeckRankCoefficientIndex E L) := Classical.decEq _

noncomputable local instance badProductCongruenceIndexFintype (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedCongruenceCoefficientIndex X E inactive L) := inferInstance

noncomputable local instance badProductCongruenceIndexDecidableEq (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedCongruenceCoefficientIndex X E inactive L) := Classical.decEq _

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

theorem allocatedMixedRank_primePower_event {N D : ℕ} [NeZero N]
    (hm : 0 < m)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
      (fun x => ∀ p : P, allocatedCongruenceModulusBad inactive noise r projection spatial kernel block
        C (p.val ^ A p.val) (fun j =>
          (allocatedMixedSelectedValues inactive x.1.val x.2 j : ZMod (p.val ^ A p.val)))) ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
          (∏ p : P, p.val ^ A p.val) / width j := by
  have h := mixedSmoothUniform_primePower_event (N := N) center width hwidth hZ P A
    hprime hcover
    (fun p => allocatedMixedModulusBad inactive noise r projection spatial kernel block C (p.val ^ A p.val))
    (fun p => by
      have ht := allocatedMixedModulusBad_probability inactive noise r projection spatial kernel block
        hm (hprime p p.property) (hpositive p p.property) hD hC (hthreshold p p.property) hL
      exact mixed_uniform_eventProbability_le_instances _ _ _ _ _ ht)
    hlarge
  simpa only [allocatedMixedModulusBad, allocatedMixedCoefficientEquiv_cast] using h

end Erdos3.VectorPolynomial
end
end OAI
