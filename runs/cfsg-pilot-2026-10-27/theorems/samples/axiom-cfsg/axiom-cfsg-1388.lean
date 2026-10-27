public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree Matrix Module

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSU)

open CFSG.RankThree.FFModules (transvectionGroup mem_transvectionGroup subOne subOne_eq_zero_iff
  range_subOne_le le_ker_subOne exists_le_transvectionGroup finrank_fin3 mulVec_mulVec_inv
  mulVec_inv_mulVec)

open scoped MatrixGroups

theorem card_center_dvd_three_of_scalar {F : Type} [Field F] [Finite F]
    {D : Subgroup (GL (Fin 3) F)} (hZ3 : ∀ z ∈ Subgroup.center D, z ^ 3 = 1)
    (hcomm : ∀ M : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) * M = M * g) → ∃ c : F, M = Matrix.scalar (Fin 3) c) :
    Nat.card (Subgroup.center D) ∣ 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.center D) := fun z => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hZ3 z z.2⟩
  obtain ⟨j, hj⟩ := hP.exists_card_eq
  have hscal : ∀ z : Subgroup.center D, (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) ((((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) := by
    intro z
    obtain ⟨c, hc⟩ := hcomm (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) fun g hg => by
      have h1 := Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩
      have h2 := congrArg (fun x : D => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h1
      simpa using h2
    rw [hc]
    simp
  have hroot : ∀ z : Subgroup.center D, (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 ∈
      (Polynomial.nthRoots 3 (1 : F)).toFinset := by
    intro z
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
    have h3 : (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
      have h1 := hZ3 z z.2
      have h2 := congrArg (fun x : D => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h1
      simpa using h2
    rw [hscal z, ← map_pow] at h3
    have h4 := congrFun (congrFun h3 0) 0
    simpa using h4
  let f : Subgroup.center D → (Polynomial.nthRoots 3 (1 : F)).toFinset := fun z => ⟨_, hroot z⟩
  have hf : Function.Injective f := by
    intro z z' h
    have h1 : (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 =
        (((z' : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 := congrArg Subtype.val h
    have h2 : (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (((z' : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [hscal z, hscal z', h1]
    exact Subtype.ext (Subtype.ext (Units.ext h2))
  have hle : Nat.card (Subgroup.center D) ≤ 3 := by
    calc Nat.card (Subgroup.center D)
        ≤ Nat.card (Polynomial.nthRoots 3 (1 : F)).toFinset := Nat.card_le_card_of_injective f hf
      _ = (Polynomial.nthRoots 3 (1 : F)).toFinset.card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ Multiset.card (Polynomial.nthRoots 3 (1 : F)) := Multiset.toFinset_card_le _
      _ ≤ 3 := Polynomial.card_nthRoots 3 1
  rw [hj] at hle ⊢
  have hj1 : j ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (pow_dvd_pow 3 hj1).trans (by norm_num)

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
end
