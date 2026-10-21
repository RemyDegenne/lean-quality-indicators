namespace OAI

namespace CubeShuffle

lemma palindromeCost_le_crowded (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeCost d e ω ≤ d*crowdedMass (Fintype.card ι) := by
  classical
  induction d generalizing ι with
  | zero => simp [palindromeCost]
  | succ d ih =>
    let σ := benesStepEquiv d ω
    let x := e.trans (headTailEquiv d).toEmbedding
    let c := PairRouting.colors x σ.2.1
    let hc := PairRouting.colors_compatible x σ.2.1
    have h₀ := ih (PairRouting.childEmbedding x c hc false) σ.1.1
    have h₁ := ih (PairRouting.childEmbedding x c hc true) σ.1.2
    have hz := alternatingCycles_le_crowded (PairRouting.switchedEmbedding x σ.2.1)
      (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1))
    have hs := crowdedMass_add (Fintype.card {i // c i = false})
      (Fintype.card {i // c i = true})
    rw [PairRouting.color_card_add] at hs
    change PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
        (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) +
        palindromeCost d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeCost d (PairRouting.childEmbedding x c hc true) σ.1.2 ≤ _
    nlinarith

end CubeShuffle
end OAI
