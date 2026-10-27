public section

namespace CFSG.ComponentClassification.GrSLit.HeLay

open CFSG Subgroup CFSG.Quasithin

open scoped commutatorElement

variable {Y T : Type*} [Group Y] [Finite Y] [Group T] [Finite T]

theorem commute_of_perfect_of_card_four {N K : Subgroup Y} [K.Normal] (hN : ⁅N, N⁆ = N)
    (hK : Nat.card K = 4) : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ = k := by
  classical
  let F : Subgroup (MulAut ↥K) := N.map (MulAut.conjNormal : Y →* MulAut ↥K)
  have : Group.IsPerfect ↥N := isPerfect_iff.mpr hN
  have hFp : Group.IsPerfect ↥F := Group.IsPerfect.map _
  have hFcard : Nat.card ↥F ∣ 24 := by
    have h1 : Nat.card ↥(F.map (MulAut.toPerm ↥K)) = Nat.card ↥F :=
      card_map_of_injective (fun a b h =>
        MulEquiv.ext fun x => congrArg (fun e : Equiv.Perm ↥K => e x) h)
    have h2 : Nat.card (Equiv.Perm ↥K) = 24 := by
      have : Fintype ↥K := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hK]
      rfl
    rw [← h1, ← h2]
    exact card_subgroup_dvd_card _
  have hsol : Group.IsSolvable ↥F := by
    refine LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    have h1 : (Nat.card ↥F).primeFactors ⊆ (24 : ℕ).primeFactors :=
      Nat.primeFactors_mono hFcard (by norm_num)
    have h2 : (24 : ℕ).primeFactors.card = 2 := by
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_pow _ (by norm_num), Nat.Prime.primeFactors Nat.prime_two,
        Nat.Prime.primeFactors Nat.prime_three]
      rfl
    exact (Finset.card_le_card h1).trans h2.le
  have hFbot : F = ⊥ := by
    by_contra hne
    have : Nontrivial ↥F := (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable _ hsol
  intro n hn k hk
  have h1 : MulAut.conjNormal n ∈ F := mem_map_of_mem _ hn
  rw [hFbot, mem_bot] at h1
  have h2 := congrArg (fun e : MulAut ↥K => ((e ⟨k, hk⟩ : ↥K) : Y)) h1
  simpa [MulAut.conjNormal_apply] using h2

end CFSG.ComponentClassification.GrSLit.HeLay
end
