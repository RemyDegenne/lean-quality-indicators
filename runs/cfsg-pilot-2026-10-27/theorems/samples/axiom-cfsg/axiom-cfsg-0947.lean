public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.TBLit

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

open CFSG.ComponentClassification.Burgoyne.Proj

open CFSG.ComponentClassification.Burgoyne.O

open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat
  conj_injective_of_mulEquiv)

open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)

variable {K : Type} [Field K] {d : ℕ}

variable [Finite K]

theorem torus_shape (hK : ringChar K ≠ 2) (hd : 7 ≤ d) (hdodd : Odd d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)} (hJ2 : J.card = 2) (hNFc : BlockNF w Jᶜ)
    (hker : OKer (oQ (diagGL hw))) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ (diagGL hw))))
    {t : X} (hsurj : OSurjX θ t)
    (ht : socleAction θ t = oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) :
    oddCentralizerCore t = ⊥ ∨ OddShape θ t := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hψ := socleAction_injective hsimple hnab θ
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  have hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ (socleAction θ).range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction _ x
  have hcore := (hsurj.core hsimple hnab).of_eq ht
  have hJd : 2 * J.card ≠ d := by
    obtain ⟨k, hk⟩ := hdodd
    omega
  have hJc5 : 5 ≤ Jᶜ.card := by
    have := card_compl_add J
    omega
  have hJc : BlockOK K w Jᶜ := hNFc.blockOK (by omega) (fun h => by omega)
  have hmem : ∀ x ∈ oddCentralizerCore t,
      socleAction θ x ∈ oddCoreIn (socleAction θ).range (oκ _ (sgnPair h2 hw J)) := by
    intro x hx
    rw [← ht, ← map_oddCentralizerCore_of_injective hψ]
    exact ⟨x, hx, rfl⟩
  by_cases h3 : Nat.card K = 3
  · left
    have hbot := split_two_oddCoreIn_eq_bot_three h3 hK hw hker hcore hinj hB hJ2 hJd hJc
    rw [eq_bot_iff]
    intro x hx
    have h1 := hmem x hx
    rw [hbot, mem_bot, ← map_one (socleAction θ)] at h1
    exact hψ h1
  · right
    refine ⟨suppOn K J, (finrank_suppOn_le J).trans hJ2.le, fun x hx => ?_⟩
    obtain ⟨R, hR, hRJ, hRx⟩ := split_two_oddCoreIn hK hw hker hcore hinj hB hJd hJc (hmem x hx)
    exact ⟨R, hR, hRx, sub_one_mulVec_mem_suppOn hw hRJ⟩

end CFSG.ComponentClassification.Burgoyne.C
end
