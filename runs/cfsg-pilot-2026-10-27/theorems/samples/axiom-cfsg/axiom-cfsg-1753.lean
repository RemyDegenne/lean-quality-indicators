public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T (vecProd vecProdHom vecProdHom_apply)

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T (listVec exists_normVec_ker_mem)

open Timmesfeld.Co1Leaf (normVecs kerBasis)

section SubTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem false_of_comp_sub (F : ModGL τ L →* ModGL τ L)
    (hFT : ∀ a : Fin τ.rank → Lˣ, F (rootDiagUnit τ a) = (rootDiagUnit τ a)⁻¹ ^ 2)
    (hFα : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ μ : Lˣ, ∀ A : Matrix.SpecialLinearGroup (Fin 2) L,
      F (rootSL2 τ L α A) = rootSL2 τ L α (conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A)))
    {G : Subgroup (ModGL τ L)} [Finite G] (hGF : G ≤ fixModel F)
    {ω : Lˣ} (hω : orderOf ω = 3) {m : ℕ} {e : Fin m → Fin τ.rank → ZMod 3}
    (he : ∀ i, dV (τ := τ) ω (e i) ∈ G) (heinj : Function.Injective (subLin (τ := τ) e))
    (hdata : ∀ fl ∈ normVecs 3 m,
      (familyKernel (famV (τ := τ) ω ((kerBasis 3 fl).map (liftL e))) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω ((kerBasis 3 fl).map (liftL e))), w = 1) ∨
      ∃ α, IsRoot τ α ∧ familyKernel (famV (τ := τ) ω ((kerBasis 3 fl).map (liftL e))) = {α, -α} ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω ((kerBasis 3 fl).map (liftL e))),
          w = 1 ∨ w = rootReflection α)
    (hdata0 : familyKernel (famV (τ := τ) ω ((Native.stdBasis m).map (liftL e))) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω ((Native.stdBasis m).map (liftL e))), w = 1)
    (h5 : ¬ 5 ^ 9 ∣ Nat.card G) {t : ModGL τ L}
    (ht : ∀ y, dV (τ := τ) ω (subLin e y) * t = t * dV ω (subLin e y)) {K : Subgroup G}
    (hK : CFSG.Open.IsComponentOf K ((Subgroup.centralizer ({t} : Set (ModGL τ L))).subgroupOf G))
    (hA5 : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) : False := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hcomm := genS_comm hω3 he
  have hpow := genS_pow hω3 he
  set φ := vecProdHom (genS he) hcomm hpow with hφdef
  have hφ : ∀ a, φ (Multiplicative.ofAdd a) = dS hω3 he a := fun a => vecProd_genS hω3 he a
  have hinj : Function.Injective φ := by
    intro a b h
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, hφ, hφ] at h
    have := heinj (dV_injective (τ := τ) hω (congrArg Subtype.val h))
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, this]
  have hGC : G ≤ adjointGroup τ L := hGF.trans inf_le_left
  have hX3 : ∀ g ∈ G, g ∈ torusGroup τ L → g ^ 3 = 1 := by
    intro g hg hgT
    obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hgT
    have hF : F (rootDiagUnit τ a) = rootDiagUnit τ a := (hGF hg).2
    rw [hFT, inv_pow] at hF
    change rootDiagUnit τ a ^ 3 = 1
    rw [pow_succ]
    exact inv_eq_iff_mul_eq_one.1 hF
  have hleaf : ∀ kb : List (List ℕ),
      ((familyKernel (famV (τ := τ) ω (kb.map (liftL e))) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω (kb.map (liftL e))), w = 1) ∨
      ∃ α, IsRoot τ α ∧ familyKernel (famV (τ := τ) ω (kb.map (liftL e))) = {α, -α} ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω (kb.map (liftL e))), w = 1 ∨
          w = rootReflection α) →
      ∀ x : G, (∀ b ∈ kb, dS hω3 he (listVec m b) * x = x * dS hω3 he (listVec m b)) →
        x ^ 18 = 1 := by
    intro kb hdat x hx
    have hxC : (x : ModGL τ L) ∈ familyCentralizer τ L (famV (τ := τ) ω (kb.map (liftL e))) := by
      refine mem_familyCentralizer_of_commute (hGC x.2) fun b hb => ?_
      obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
      rw [listVec_liftL]
      exact congrArg Subtype.val (hx b' hb')
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine pow_eighteen_of_mem_familyCentralizer hX3 ?_ x.2 hxC
    rcases hdat with h | ⟨α, hα, hker, hW⟩
    · exact Or.inl h
    · obtain ⟨μ, hμ⟩ := hFα α hα
      refine Or.inr ⟨α, hα, hker, hW, fun g hg hgTL => ?_, fun g hg hgL =>
        pow_six_eq_one_of_twFix F hα hμ (hGF hg).2 hgL⟩
      exact pow_three_mem_rootSpan_tw F hFT hα hμ (hGF hg) hgTL
  set C : Subgroup G := (Subgroup.centralizer ({t} : Set (ModGL τ L))).subgroupOf G with hCdef
  have hAC : φ.range ≤ C := by
    rintro _ ⟨a, rfl⟩
    rw [← ofAdd_toAdd a, hφ, hCdef, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ht _
  refine false_of_torus_comp hcomm hpow hinj hAC hK hA5 ?_ ?_ ?_
  · intro x _ hx
    exact hleaf (Native.stdBasis m) (Or.inl hdata0) x fun b _ =>
      hx (dS hω3 he (listVec m b)) ⟨Multiplicative.ofAdd _, hφ _⟩
  · intro fl hfl x _ hx
    refine hleaf (kerBasis 3 fl) (hdata fl hfl) x fun b hb => ?_
    have h1 := hx b hb
    rwa [vecProd_genS hω3 he] at h1
  · intro h
    exact h5 (h.trans (Subgroup.card_subgroup_dvd_card C))

end SubTorus
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k
end
