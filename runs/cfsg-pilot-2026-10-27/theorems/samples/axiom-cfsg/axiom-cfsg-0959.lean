public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  Multiplicative CFSG.HardMathSupport.Curtis.UnitaryLevi CFSG.ComponentClassification

open CFSG.RankThree.CALinearPlane

variable {F : Type} [Field F] {f m ε p : ℕ} {h : UnitaryFieldData 2 f F}

theorem hypBlock_zeroCoords_le_centralizer {ζ : F}
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E : Set (Multiplicative (Fin m → ZMod p))} {S : Finset (Fin m)}
    (hS : ∀ i ∈ S, ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = 0) :
    hypBlock h (zeroCoords (ε := ε) S) ≤ Subgroup.centralizer (τ '' E) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨t, ht, rfl⟩
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  have hτt : (((τ t : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) =
      diagonal (splitEntries ζ (Multiplicative.toAdd t)) := hτ (Multiplicative.toAdd t)
  rw [hτt]
  have hentry : ∀ x ∈ zeroCoords (ε := ε) S,
      splitEntries ζ (Multiplicative.toAdd t) x = 1 :=
    fun x hx => splitEntries_eq_one_of_mem_zeroCoords
      (fun i hi => hS i hi (Multiplicative.toAdd t) ht) hx
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hD : splitEntries ζ (Multiplicative.toAdd t) a =
      splitEntries ζ (Multiplicative.toAdd t) b
  · rw [hD, mul_comm]
  · have hne : a ≠ b := fun hab => hD (by rw [hab])
    have hgab : (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) a b = 0 := by
      by_cases ha : a ∈ zeroCoords (ε := ε) S
      · by_cases hb : b ∈ zeroCoords (ε := ε) S
        · exact absurd (by rw [hentry a ha, hentry b hb]) hD
        · rw [mem_hypBlock.mp hg a b (Or.inr hb), Matrix.one_apply_ne hne]
      · rw [mem_hypBlock.mp hg a b (Or.inl ha), Matrix.one_apply_ne hne]
    rw [hgab, zero_mul, mul_zero]

end CFSG.StandardType.SuSplitRootGen
end
