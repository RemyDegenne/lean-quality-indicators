public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 RootSpace

theorem three_dvd_ncard_of_free {τ : Tag} {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite)
    {w : WeylGroup τ} (hw3 : w ^ 3 = 1) (hmaps : ∀ x ∈ S, w • x ∈ S)
    (hfree : ∀ x ∈ S, w • x ≠ x) : 3 ∣ S.ncard := by
  classical
  have : Fintype S := hS.fintype
  have hthree : ∀ x : Fin τ.rank → ℤ, w • w • w • x = x := fun x => by
    rw [smul_smul, smul_smul, ← pow_three', hw3, one_smul]
  have hmem : ∀ x, w • x ∈ S ↔ x ∈ S := fun x =>
    ⟨fun h => by
      have h2 := hmaps _ (hmaps _ h)
      rwa [hthree] at h2, fun h => hmaps x h⟩
  let σ : Equiv.Perm S := (MulAction.toPerm w).subtypePerm fun x => hmem x
  have hσ : ∀ x : S, (σ x : Fin τ.rank → ℤ) = w • (x : Fin τ.rank → ℤ) := fun x => rfl
  have hσ3 : σ ^ 3 ^ 1 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [pow_one, pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ, hσ,
      hσ, hthree]
    rfl
  have hsupp : σ.supportᶜ.card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hx
    exact hfree x x.2 (congrArg Subtype.val hx ▸ (hσ x).symm)
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) hσ3
  rw [hsupp] at hmod
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd.1 hmod.symm)

end CFSG.RankThree.Lattice
end
