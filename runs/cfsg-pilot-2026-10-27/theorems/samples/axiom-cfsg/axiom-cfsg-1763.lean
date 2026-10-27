public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native

theorem co3KAllProd3_spec
    {p : Array ℕ → Bool} (h : co3KAllProd3 co3TLevels p = true) {x : Equiv.Perm (Fin 276)}
    (hx : x ∈ co3T) : ∃ g : Array ℕ, Rep 276 g x ∧ p g = true := by
  have hF := chainCheckFacts co3TChain_check.1
  obtain ⟨a, ha, b, hb, c, hc', hprod⟩ := ChainArrays.exists_prod3 co3TArrays (by norm_num)
    co3TChain_check.1 (by decide) (fun i h3 hi => absurd hi (by
      change ¬ i < 3; omega)) hx
  have h0 : (0 : ℕ) < co3TChain.baseCount := by decide
  have h1 : (1 : ℕ) < co3TChain.baseCount := by decide
  have h2 : (2 : ℕ) < co3TChain.baseCount := by decide
  rw [co3KAllProd3] at h
  refine ⟨compA 276 (compA 276 (co3TLevels[0]!).tr[a]! (co3TLevels[1]!).tr[b]!)
    (co3TLevels[2]!).tr[c]!, ?_, allLt_spec (allLt_spec (allLt_spec h ha) hb) hc'⟩
  rw [← hprod]
  exact rep_compA (rep_compA (co3TArrays.rep_levT hF h0 ha) (co3TArrays.rep_levT hF h1 hb))
    (co3TArrays.rep_levT hF h2 hc')

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K
end
