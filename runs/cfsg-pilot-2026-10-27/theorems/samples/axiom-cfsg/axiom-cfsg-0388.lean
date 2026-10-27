public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256i

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

section ReeGen37

open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

open CFSG.RankThree.PartOne.CTP (FieldAutData IsOuterOfOrder)

theorem exists_fixSubgroup_equiv_reeGamma_zero (hv : (TauCeti.LieTypeIndex.reeG2 3).Valid)
    (y : MulAut (CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 3, hv⟩)) (hy : IsOuterOfOrder 7 y) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k ReeTag.G2.prime),
      Nat.card k = 3 ^ (2 * 0 + 1) ∧ Nonempty (↥(fixSubgroup y) ≃* ReeTag.G2.reeGamma k 0) := by
  obtain ⟨X, _, _, _, hm1, hX, ⟨e⟩⟩ := CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.exists_reeG2_model
    (K := CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 3, hv⟩) ⟨hv, ⟨MulEquiv.refl _⟩⟩
  set y' := MulAut.congr e y with hy'
  have hy'o : orderOf y' = 7 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective y).trans hy.1
  have hy'p : y' ^ 7 = 1 := by rw [← hy'o]; exact pow_orderOf_eq_one y'
  have hin : y' ∉ (MulAut.conj : ReeTag.G2.reeGamma X 3 →* MulAut (ReeTag.G2.reeGamma X 3)).range := by
    rintro ⟨g, hg⟩
    apply hy.2 (e.symm g)
    ext x
    have h1 := congrArg (fun φ : MulAut (ReeTag.G2.reeGamma X 3) => φ (e x)) hg
    simp only [hy', MulAut.conj_apply, MulAut.congr_apply] at h1
    apply e.injective
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    simpa using h1.symm
  obtain ⟨-, δ, σ, hσ, hδ, -⟩ := CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent 3 hm1 X
    hX (by norm_num) (by norm_num) y' hy'p hin
  obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hX (by norm_num) (by norm_num) hσ
  obtain rfl : b = 0 := by omega
  set σh := ReeTag.G2.reeGammaFieldAut X 3 σ with hσh
  have hy'eq : y' = MulAut.congr δ⁻¹ σh := by
    rw [CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.mulAut_congr_self, ← hδ]
    group
  let e1 : ↥(fixSubgroup y) ≃* ↥(fixSubgroup y') :=
    ((fixSubgroup y).equivMapOfInjective (e : _ →* _) e.injective).trans
      (MulEquiv.subgroupCongr (Inputs256e.fixSubgroup_congr e y).symm)
  let e2 : ↥(fixSubgroup y') ≃* ↥(fixSubgroup σh) :=
    (MulEquiv.subgroupCongr (by rw [hy'eq, Inputs256e.fixSubgroup_congr])).trans
      ((fixSubgroup σh).equivMapOfInjective ((δ⁻¹ : MulAut _) : _ →* _) (δ⁻¹ : MulAut _).injective).symm
  let e3 : ↥(fixSubgroup σh) ≃* ReeTag.G2.reeGamma (fixSubfield σ) 0 :=
    (MulEquiv.subgroupCongr
      (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.fixSubgroup_eq_fixSub _)).trans eC
  exact ⟨fixSubfield σ, inferInstance, inferInstance, hchar, hbcard, ⟨e1.trans (e2.trans e3)⟩⟩

end ReeGen37
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256i
end
