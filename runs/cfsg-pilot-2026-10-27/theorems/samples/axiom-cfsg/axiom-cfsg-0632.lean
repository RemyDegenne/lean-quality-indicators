public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

variable {G : Type} [Group G]

variable [Finite G]

omit [Finite G] in
theorem symX_facts {x : G} {K : Subgroup (CentralizerBar x)} (hxK : xbar x ∈ K)
    (hx : orderOf x = 2) {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)}
    (hf : S1Frame x K u hu) :
    (∀ i, IsConj x (symX x u i)) ∧ (∀ i, symX x u i * symX x u i = 1) ∧
      (∀ i j, symX x u i * symX x u j = symX x u j * symX x u i) ∧
        symX x u 0 * symX x u 1 * symX x u 2 * symX x u 3 * symX x u 4 = 1 ∧
          (∀ i j, i ≠ j → symX x u i ≠ symX x u j) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hf
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hxu : ∀ k, u k * x = x * u k := fun k => mem_centralizer_singleton_iff.1 (hu k)
  have hne : ∀ k, u k ≠ x := by
    intro k hk
    apply (h1 k).2.2
    have key : ∀ (a : G) (ha : a ∈ centralizer ({x} : Set G)), a = x → barOf ha = xbar x := by
      rintro a ha rfl
      rfl
    rw [key (u k) (hu k) hk]
    exact hxK
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [symX_last]
    · rw [symX_castSucc]
      exact (h1 k).1
  · intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [symX_last]
      exact hxx
    · rw [symX_castSucc]
      exact (h1 k).2.1
  · intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases rfl (fun b => ?_) j
      rw [symX_last, symX_castSucc]
      exact (hxu b).symm
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · rw [symX_last, symX_castSucc]
        exact hxu a
      · rw [symX_castSucc, symX_castSucc]
        exact h2 a b
  · rw [symX_zero, symX_one, symX_two, symX_three, symX_four, h3, hxx]
  · intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases (fun h => (h rfl).elim) (fun b => ?_) j
      intro _
      rw [symX_last, symX_castSucc]
      exact (hne b).symm
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · intro _
        rw [symX_last, symX_castSucc]
        exact hne a
      · intro hij
        rw [symX_castSucc, symX_castSucc]
        exact h4 a b (fun hab => hij (by rw [hab]))

end CFSG.GH74.Generic.S1
end
