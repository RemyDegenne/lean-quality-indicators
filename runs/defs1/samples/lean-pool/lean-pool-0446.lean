@[expose] public section

namespace MooreBound

open Module

open scoped BigOperators

namespace DegreeDiameter

section AdaptedBases

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}

/-- An adapted flag basis is exactly a linearly independent `n`-tuple. -/
noncomputable def adaptedFlagBasisEquivLinearIndependent
    [FiniteDimensional K V] (hV : finrank K V = n) :
    AdaptedFlagBasis K V n ≃
      {v : Fin n → V // LinearIndependent K v} := by
  let f : AdaptedFlagBasis K V n →
      {v : Fin n → V // LinearIndependent K v} := fun d ↦
    ⟨adaptedVectors d, adaptedVectors_linearIndependent d⟩
  apply Equiv.ofBijective f
  constructor
  · intro d e h
    have hv : adaptedVectors d = adaptedVectors e :=
      congrArg Subtype.val h
    have hflag : d.1 = e.1 := by
      apply CompleteFlag.ext
      intro r
      rw [← span_adaptedVectors_eq d r, ← span_adaptedVectors_eq e r, hv]
    cases d with
    | mk F a =>
      cases e with
      | mk G b =>
        dsimp only at hflag ⊢
        subst G
        have hab : a = b := by
          funext i
          apply Subtype.ext
          apply Subtype.ext
          exact congrFun hv i
        subst b
        rfl
  · intro s
    let b : Basis (Fin n) K V :=
      basisOfLinearIndependentOfCardEqFinrank' s.1 s.2 (by
        simp [hV])
    have hb : (b : Fin n → V) = s.1 :=
      coe_basisOfLinearIndependentOfCardEqFinrank' s.1 s.2 (by
        simp [hV])
    let F : CompleteFlag K V n := CompleteFlag.ofBasis b
    let a : FlagStepChoices F := fun i ↦
      ⟨⟨b i, b.self_mem_flag (by simp)⟩, by
        intro hmem
        exact (lt_irrefl i.castSucc) ((b.self_mem_flag_iff).mp hmem)⟩
    refine ⟨⟨F, a⟩, ?_⟩
    apply Subtype.ext
    funext i
    change b i = s.1 i
    exact congrFun hb i

end AdaptedBases
end DegreeDiameter
end MooreBound
end
