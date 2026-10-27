public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3

theorem tightEdgePairGoodS_at {n : ℕ} (hodd : TightOddLeaf n) (hconn : TightConnLeaf n)
    (hsep : TightSepLeaf n) (hthin : TightThinLeaf n) (hE3 : TightE3Leaf n) :
    TightEdgePairGoodS n := by
  intro hA hB Y _ _ hn R S t hd hc hE2 hQ hlarge hedge hZ
  have hL : TightLargeHyp n Y R S t := ⟨hA, hB, hn, hd, hc, hE2, hQ, hlarge, hedge, hZ⟩
  have hO : TightOddCent t := hodd Y R S t hL
  have hΩ := hd.hypOmegaGen
  have h2 := hd.isPGroup_member hO
  have hcn := hconn Y R S t hL hO
  have hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R)) := @hsep Y _ _ R S t hL hO
  have huniq := hd.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htr : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g (tightCore R) = J :=
    fun J hJ => hJ
  have hgen : (⨆ J ∈ CoreAssembly.conjClass (tightCore R), J) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hc.2.1
  have hF := TC.graphFam hΩ h2 hsp htr hgen hcn
  obtain ⟨J₀, hJ₀⟩ := hd.nonempty_omegaNbr_of_not_dEdgeless hedge
  obtain ⟨P, hP⟩ := exists_isMaxOrb (A := TC.nbrAdj (CoreAssembly.conjClass (tightCore R)))
    (⟨hK, hJ₀⟩ : TC.nbrAdj _ (tightCore R) J₀)
  obtain ⟨⟨J, hKJ, hJP⟩, -⟩ := id hP
  have hmax : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J :=
    ⟨hKJ, by rw [hJP]; exact hP⟩
  obtain ⟨g, hgJ'⟩ := hKJ.2.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hu : IsUniqueInvolution J (g * t * g⁻¹) := hgJ ▸ huniq.conj g
  obtain ⟨-, -, hut, htu, -⟩ := hd.edge_involution hKJ.2 hu
  refine ⟨g, hgJ ▸ hKJ.2, htu, hut, hL.good_section hodd hconn hsep hthin hE3 hmax hu htu, ?_⟩
  obtain ⟨SJ, hLJ⟩ := hL.conj g
  have hJcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hmax' : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore (conjSub g R))))
      (tightCore (conjSub g R)) (tightCore R) := by
    rw [hfam, hJcore]
    exact ⟨hF.graph.symm hmax.1, orbOf_mem_maxOrbs hF hmax.1 hmax.2⟩
  exact hLJ.good_section hodd hconn hsep hthin hE3 hmax' huniq hut

end Cit3
end CFSG.ClassicalInvolution.Q3.TL4
end
