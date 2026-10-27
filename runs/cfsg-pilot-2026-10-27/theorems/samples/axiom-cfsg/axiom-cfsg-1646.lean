open CFSG

namespace CFSG.BenderSuzuki

namespace PFchapter1section2

open PFchapter1section1 PFAppendixIII

public theorem peterfalvi_chapter1_section2_canonical_W_normal_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q V W : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hV_eq : V = peterfalviV D t)
    (hW_eq : W = peterfalviW V (peterfalviKSet D t)) :
    (W.subgroupOf D).Normal := by
  classical
  let Iset : Set G := {x : G | x ∈ H ∧ IsInvolution x}
  have hW_eq_centralizer : W = D ⊓ Subgroup.centralizer Iset := by
    simpa [Iset] using
      peterfalvi_chapter1_section2_canonical_W_eq_D_centralizer_involutions
        H D Q V W t hA1 hV_eq hW_eq
  have hWleD : W ≤ D := by
    rw [hW_eq_centralizer]
    exact inf_le_left
  rw [Subgroup.normal_subgroupOf_iff hWleD]
  intro x d hxW hdD
  rw [hW_eq_centralizer] at hxW ⊢
  refine ⟨D.mul_mem (D.mul_mem hdD hxW.1) (D.inv_mem hdD), ?_⟩
  change d * x * d⁻¹ ∈ Subgroup.centralizer Iset
  rw [Subgroup.mem_centralizer_iff]
  intro y hyI
  have hdyH : rightConjugateElem y d ∈ Iset := by
    refine ⟨?_, isInvolution_rightConjugateElem hyI.2⟩
    exact H.mul_mem
      (H.mul_mem (H.inv_mem (hA1.D_le_H hdD)) hyI.1)
      (hA1.D_le_H hdD)
  have hcomm : rightConjugateElem y d * x = x * rightConjugateElem y d :=
    (Subgroup.mem_centralizer_iff.mp hxW.2) (rightConjugateElem y d) hdyH
  calc
    y * (d * x * d⁻¹) = d * (rightConjugateElem y d * x) * d⁻¹ := by
      simp [rightConjugateElem, mul_assoc]
    _ = d * (x * rightConjugateElem y d) * d⁻¹ := by rw [hcomm]
    _ = (d * x * d⁻¹) * y := by simp [rightConjugateElem, mul_assoc]

end PFchapter1section2
end CFSG.BenderSuzuki
