namespace P2MW.S_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.longFile 0

set_option linter.style.longLine false

noncomputable section

open IsDedekindDomain NumberField

open scoped WithZero

namespace KirillovBallCutoffFn

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v

local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)

local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

scoped instance compactSpace_ball (j : ℤ) : CompactSpace (ball K v j) :=
  isCompact_iff_compactSpace.mp (isCompact_ball j)

scoped instance finite_Q (j k : ℤ) : Finite (Q K v j k) :=
  AddSubgroup.quotient_finite_of_isOpen _ (AddSubgroup.addSubgroupOf_isOpen _ _ (isOpen_ball k))

scoped instance fintype_Q (j k : ℤ) : Fintype (Q K v j k) := Fintype.ofFinite _

theorem exists_level (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (m₀ : ℤ)
    (hm₀ : ∀ x : F, Valued.v x ≤ WithZero.exp m₀ → ψ x = 1) :
    ∃ ℓ : ℤ, (∀ x : F, Valued.v x ≤ WithZero.exp ℓ → ψ x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp (ℓ + 1) ∧ ψ x ≠ 1 := by
  classical
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : F, ψ x₁ ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (DFunLike.ext ψ 1 fun x => by rw [h x, AddChar.one_apply])
  have hx₁0 : Valued.v x₁ ≠ 0 := by
    intro h0
    apply hx₁
    exact hm₀ x₁ (by rw [h0]; exact zero_le')
  set M : ℤ := WithZero.log (Valued.v x₁) with hM
  have hvx₁ : Valued.v x₁ = WithZero.exp M := by rw [hM, WithZero.exp_log hx₁0]
  let P : ℤ → Prop := fun m => ∀ x : F, Valued.v x ≤ WithZero.exp m → ψ x = 1
  have hPM : ¬ P M := fun h => hx₁ (h x₁ hvx₁.le)
  have hmono : ∀ m m' : ℤ, m' ≤ m → P m → P m' := fun m m' hle h x hx =>
    h x (hx.trans (WithZero.exp_le_exp.mpr hle))
  have hlt : m₀ < M := by
    by_contra hle
    push Not at hle
    exact hPM (hmono _ _ hle hm₀)
  have key : ∀ n : ℕ, P (m₀ + n) → ¬ P (m₀ + n + 1) →
      ∃ ℓ : ℤ, P ℓ ∧ ∃ x : F, Valued.v x ≤ WithZero.exp (ℓ + 1) ∧ ψ x ≠ 1 := by
    intro n hn hn1
    refine ⟨m₀ + n, hn, ?_⟩
    by_contra h
    push Not at h
    exact hn1 fun x hx => h x hx
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M = m₀ + N + 1 := ⟨(M - m₀ - 1).toNat, by omega⟩
  have : ∃ n : ℕ, n ≤ N ∧ P (m₀ + n) ∧ ¬ P (m₀ + n + 1) := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ n : ℕ, n ≤ N + 1 → P (m₀ + n) := by
      intro n
      induction n with
      | zero => intro _; simpa using hm₀
      | succ n ih =>
        intro hn
        have h := hcon n (by omega) (ih (by omega))
        push_cast
        rwa [← add_assoc]
    have := hall (N + 1) le_rfl
    apply hPM
    rw [hN]
    push_cast at this
    rwa [← add_assoc] at this
  obtain ⟨n, -, hn, hn1⟩ := this
  exact key n hn hn1

end KirillovBallCutoffFn
end
end P2MW.S_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
