public noncomputable section

namespace CFSG.StandardType.QTwo

section Diagonal

open CFSG.StandardType

open CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

open scoped MatrixGroups

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

section NativeNormalization

variable {G : Type} [Group G] [Finite G]

variable {m : ℕ} {ψ : Su F0 2 1 m →* G}

theorem qTwoFour_indicator_comm_of_map_comm (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m)
    {I : Finset (Fin m)} (hI : I.card = 4) {j : Fin m} (hj : j ∉ I)
    {ω : F0} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hω0 : ω ≠ 0)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m))
    {t v : Su F0 2 1 m}
    (htmat : ((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1))
    (hcomm : ψ v * ψ t = ψ t * ψ v) :
    compIndicator F0 I * ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      ((v : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) * compIndicator F0 I := by
  classical
  have htrace : (((t : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)).trace ≠ 0 :=
    qTwoFour_separating_trace_ne_zero hI hj hω3 hω1 htmat
  have hvt : v * t = t * v :=
    qTwoFour_comm_of_map_comm_of_trace_ne_zero hF0 (by omega : 4 ≤ m) ψ hker htrace hcomm
  have hsep : ∀ i ∈ I, ∀ j' ∉ I,
      (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) i ≠
        (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) j' := by
    intro i hi j' hj'
    have hdi : (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) i = ω := by
      simp [hi]
    have hω2ne : ω ≠ ω ^ 2 := by
      intro h
      have h1 : ω * 1 = ω * ω := by
        rw [mul_one]
        simpa [pow_two] using h
      exact hω1 (mul_left_cancel₀ hω0 h1).symm
    by_cases hjj : j' = j
    · have hdj : (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) j' = ω ^ 2 := by
        simp [hj', hjj, hj]
      rw [hdi, hdj]
      exact hω2ne
    · have hdj : (fun i => if i ∈ I then ω else if i = j then ω ^ 2 else 1) j' = 1 := by
        simp [hj', hjj]
      rw [hdi, hdj]
      exact hω1
  exact qTwoFour_compIndicator_comm_of_comm_diagonal (d := fun i =>
    if i ∈ I then ω else if i = j then ω ^ 2 else 1) htmat hvt hsep

end NativeNormalization
end Diagonal
end CFSG.StandardType.QTwo
end
