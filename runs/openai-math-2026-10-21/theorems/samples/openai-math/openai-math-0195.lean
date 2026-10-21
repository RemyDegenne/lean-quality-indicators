namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteNestedSourceNative_budget
    {outerDepth innerDepth cutoff : ℕ} (m : ℕ) (G : Type) [Fintype G]
    (count nX A Cdirect : ℕ) (constants : ℕ → ℕ)
    {Bstruct pnum Qstride gainLog stageLog : ℝ}
    (hcutoff : cutoff ≤ m) (hA : 2 ≤ A) (hB : 0 ≤ Bstruct)
    (hnum : pnum ∈ Set.Icc 0 Bstruct) (hstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct)
    (hcount : (count : ℝ) ≤ Bstruct) (hnX : (nX : ℝ) ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (Plate : ℝ) (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    let seed := preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k
    let stage := (preparedFiniteNestedForwardAllDegreeStage k).val
    let C := preparedFiniteNestedSourceNativeExponent m cutoff Cdirect
    preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate k ∈ Set.Icc 0
        ((preparedFiniteForwardSourcePrecision A constants stage seed gainLog stageLog +
          preparedFiniteForwardWork A constants stage seed + C) ^ C) := by
  intro seed stage C
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cresource := preparedFiniteForwardActualNativeBudgetExponent m Pdetect
  have hseed : Bstruct ≤ seed :=
    le_preparedFiniteNestedForwardAllDegreeSeed A constants hA hB k
  have hseed0 : 0 ≤ seed := hB.trans hseed
  have hg' : gainLog ∈ Set.Icc 0 seed := ⟨hg.1, hg.2.trans hseed⟩
  have hs' : stageLog ∈ Set.Icc 0 seed := ⟨hs.1, hs.2.trans hseed⟩
  let d : Fin (m + 1) := ⟨preparedFiniteNestedForwardAllDegreeDegree k,
    Nat.lt_succ_of_le (preparedFiniteNestedForwardAllDegreeDegree_le hcutoff k)⟩
  have hresource := (Classical.choose_spec (exists_preparedFiniteForwardActualNativeBudget m Pdetect)).2
    d A Cdirect constants stage (preparedFiniteNestedForwardAllDegreeIsDirect k)
    (G := G) hA hseed0 hg' hs'
    ⟨hB, hseed⟩ ⟨hnum.1, hnum.2.trans hseed⟩ ⟨hB, hseed⟩
    ⟨hstride.1, hstride.2.trans hseed⟩
    (hcount.trans hseed) (hnX.trans hseed) (hG.trans hseed) Plate
  have hn := hresource.2.2.1
  refine ⟨hn.1, hn.2.trans ?_⟩
  exact preparedFiniteForwardAllSlotResource_budget A Cdirect Cresource constants stage
    (preparedFiniteNestedForwardAllDegreeIsDirect k) hseed0 hg' hs'

end Erdos3.VectorPolynomial
end
end OAI
