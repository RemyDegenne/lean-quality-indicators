public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf

open CFSG.ClassicalInvolution.RouteD.Exotic (ChainOK)

open CFSG.ClassicalInvolution.Generic (Commutes)

open CFSG.ClassicalInvolution.RouteD (hiF4 isRoot_hiF4 rankOneHiF4 commutes_rankOneHiF4
  commutes_iSup_left)

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open scoped MatrixGroups

theorem excCompModel_f4_toral_B4_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K)
    {M : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsB4))} (hM : IsComponent M) :
    ExcCompModel p M := by
  classical
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hq4 : 4 ≤ Nat.card K := by omega
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨hp, hf, by norm_num, hp2⟩
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _
      (bitsTuple_mem (K := K) f4BitsB4)
  have hker : rootCharKernel (bitsTuple (K := K) f4BitsB4) =
      kernelRoots (maskChar (τ := .F4) f4BitsB4) := by
    rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_B4_F4 hp hp2 hK hq4 h2
  have hSim : (⨆ k, b4Chain K k).map (adjointGroup .F4 K).subtype =
      rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) := by
    rw [map_subtype_iSup_b4Chain, hker]
  let e₁ : ↥(⨆ k, b4Chain K k) ≃* rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) :=
    ((⨆ k, b4Chain K k).equivMapOfInjective _ (adjointGroup .F4 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hSim)
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁.symm).symm hqs
  have hMeq := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  let e : M ≃* ↥(⨆ k, b4Chain K k) := (MulEquiv.subgroupCongr hMeq).trans (e₂.trans e₁.symm)
  exact ⟨.POmegaOdd, 4, f, (by unfold ExcCompTag; decide), hadm, lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie⟩

end CFSG.ComponentClassification.Burgoyne.X10
end
