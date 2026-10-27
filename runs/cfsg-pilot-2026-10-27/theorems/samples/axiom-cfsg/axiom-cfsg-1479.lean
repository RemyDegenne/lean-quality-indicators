public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)

open CFSG.LieType.Chevalley

open CFSG.LieType.Ree (ReeTag)

open CFSG.Blueprint.Chevalley CFSG.Blueprint

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

open CFSG.Sporadic.Co2Smith (Sp62 natCard_sp62)

open CFSG.HardMathSupport.Timmesfeld.DefChar (nonempty_mulEquiv_adjoint_of_bridge)

theorem cube_d4two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Yardstones.Md0ec50421ce4.catalogIs S S9.isD4two) (h : p ^ 3 ∣ Nat.card (MulAut S)) :
    False := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isD4two hS
  obtain ⟨eO⟩ := CFSG.AGLEmbedding.O8pCent.nonempty_mulEquiv_omegaT_catalog ⟨.D 4 q, hv⟩ q hq rfl
  let eS : S ≃* CFSG.EvenSmallLie.OmegaEight.omegaT := e.trans eO
  have hO : Nat.card (Outer S) ∣ 12 := by
    have hc : Nat.card (Outer S) = Nat.card (Outer CFSG.EvenSmallLie.OmegaEight.omegaT) :=
      Nat.card_congr (equivalence eS).toEquiv
    rw [hc, CFSG.EvenSmallLie.OmegaEight.card_outer_omegaT]
    norm_num
  have hSc : Nat.card S = 174182400 := by
    rw [Nat.card_congr eS.toEquiv, CFSG.EvenSmallLie.OmegaEight.card_omegaT]
  have h' := cube_dvd_of_outer_dvd hp h5 hO h
  rw [hSc] at h'
  exact cube_ndvd_Om8 hp h5 h'

end CFSG.LocalAnalysis.GLTheoremA
end
