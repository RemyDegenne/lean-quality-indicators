namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma prefix_tail_support {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)}
    (hPH : P H < H) (hHm : H ≤ m x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (hζ : IsPrefixDatum x H ζ) :
    IsTotient ζ.d ∧ ζ.d ∈ Finset.Icc 1 (tailValueBound H) := by
  obtain ⟨η, hη, hd, _⟩ := hζ
  let η' := extractTail x H η
  have hw : IsWitness H (theta x) η' := extractTail_isWitness hη hPH hHm
  have hwd : (w η').totient = ζ.d := by
    rw [extractTail_value η hPH.le hHm]
    exact hd
  have hdt : IsTotient ζ.d := ⟨w η', witness_w_pos hw, hwd⟩
  refine ⟨hdt, Finset.mem_Icc.mpr ⟨isTotient_pos hdt, ?_⟩⟩
  exact witness_totient_bound hs η' ⟨hw, hwd⟩

end TotientAsymptotic
end
end OAI
