public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.F4Model

theorem ggSecFiveRowJoinOffQAt_F4_of_reflMaxAt
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hTBF : GGTBFixInput)
    (hFC : GGResNbrFixCentralizesInput) (hRM : GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M) :
    GGSecFiveRowJoinOffQAt fun M => GGIsWeylMatrixF4 M := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 hQ ι M e hP hF
  have hFixL : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) →
      (b : G) ∈ Subgroup.zpowers x := fun b hb =>
    ((GGSecFiveRestHyp.fixLineComp_L hTBF hR.1 hR.2.1).fix_iff b).1 hb
  have hWL : GGWeylReflectionGroup p (ggAutomizer L Bs) :=
    GGSecFiveRestHyp.weylReflectionGroup_L hX hTCJ hRig hR.1 hR.2.1
  have hRM' : ∀ y K, GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 := fun y K hn =>
    hRM G p B Bs x L D J 𝒦 hR ι M e hP hF y K hn
  have hWK : ∀ y K, GGNbr p B x D J y K →
      GGWeylReflectionGroup p (ggAutomizer K Bs) := fun y K hn =>
    GGSecFiveRestHyp.weylReflectionGroup_nbr hX hTCJ hRig hTPn hA8 hraw hiso hR.1 hR.2.1 hn
  have hF1 : ∀ y K, GGNbr p B x D J y K → ∀ b : ↥Bs,
      (∀ a ∈ ggAutomizer K Bs, a b = b) → (b : G) ∈ Subgroup.centralizer (K : Set G) :=
    fun y K hn b hb =>
      hFC G p B Bs x L D J y K
        ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hn, hR.2.1 y K hn, Or.inr hR.2.1⟩ b hb
  exact ggSecFiveF4Join_of_suppliers hR hP hF hFixL hWL hRM' hWK hF1

end CFSG.StandardType
end
