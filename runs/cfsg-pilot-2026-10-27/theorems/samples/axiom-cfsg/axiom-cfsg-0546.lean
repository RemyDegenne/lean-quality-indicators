public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims136

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut localDeltaIn)

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (mem_gLAPPrimeCoreOf_iff)

open scoped commutatorElement

theorem iiHard_of_inputs' (hI191 : Lemma129.Input19_1_two) (hI1916 : Input19_16Three)
    (hRed : Lemma136c.IIHardReduction) (hCase : Lemma136c.IIHardCases) : Lemma136.IIHardInput := by
  have hF := centralizerFStarFact_holds
  have hI191' := input19_1_O2_of_input19_1_two hI191
  unfold Lemma136c.IIHardReduction at hRed
  unfold Lemma136c.IIHardCases at hCase
  unfold Lemma136c.CentralizerFStarFact at hF
  intro G _ _ m B M E A D T L h hN d hd hd1 hfix
  haveI : IsSimpleGroup G := h.standing.simple
  obtain ⟨b, B1, hPD, hsetup⟩ := hRed G m h hN hd hd1 hfix
  have hs := hsetup
  obtain ⟨-, ⟨r, hr, hEk⟩, hS1Δ, hS1P, hS1C, hred⟩ := hsetup
  have hX : Cg d ≠ ⊤ := Lemma136c.l136c_centralizer_ne_top h.standing.nonabelian hd1
  have hI := hI191' G h.standing.kProper 3 Nat.prime_three (by norm_num) r (by omega) (Cg d)
    (Lemma136c.bStarOf B L D b) hX hEk
  have hS1O : Lemma136c.s1Of B L D d b B1 ≤ GLAPPrimeCoreOf 3 (Cg d) := by
    by_contra hne
    obtain ⟨K, hK, hnot⟩ : ∃ K : Subgroup G, GLAPComponent 3 (Cg d) K ∧
        ¬ ⁅K, Lemma136c.s1Of B L D d b B1⁆ ≤ GLAPPrimeCoreOf 3 (Cg d) := by
      by_contra hall
      push Not at hall
      exact hne (hF G (Cg d) (Lemma136c.s1Of B L D d b B1) hS1C hS1P
        (fun K hK => hS1Δ.trans (hI.1 K hK))
        (fun y hy z hz => hI.2.1 y (hS1Δ hy) z hz) hall)
    have hnotΔ : ¬ ⁅K, localDeltaTwoIn (Cg d) (Lemma136c.bStarOf B L D b)⁆ ≤
        GLAPPrimeCoreOf 3 (Cg d) :=
      fun hle => hnot ((Subgroup.commutator_mono le_rfl hS1Δ).trans hle)
    obtain ⟨hBsN, hcent, hnb⟩ := hI.2.2 K hK hnotΔ
    have hKtop : K ≠ ⊤ := fun htop => hX (top_le_iff.1 (htop ▸ hK.1))
    have hKG : CFSG.Open.IsKGroup (barOf 3 K) :=
      (CFSG.Open.IsKProper.isKGroup h.standing.kProper K hKtop).quotient (GLAPPrimeCore 3 ↥K)
    have halt := alt_of_component hI1916 hr hKG hK hEk hBsN hcent hnb
    exact hCase G m h hN hd hd1 hfix b B1 hPD hs r hr hEk K hK hnot hBsN hcent halt
  exact hred.trans (sup_le hS1O le_rfl)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims136
end
