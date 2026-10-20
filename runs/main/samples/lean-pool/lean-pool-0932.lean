public section

namespace ParallelPostulate

namespace HyperbolicPlane

open Pairs

section Bound

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem exists_beyond (κ : K) {A C : K × K} (hAC : A ≠ C) (hC : C ∈ plane κ) :
    ∃ B : K × K, B ∈ plane κ ∧ Between A C B := by
  obtain ⟨s, hs, hB⟩ :=
    plane_open_forward κ ⟨C, (C.1 + (C.1 - A.1), C.2 + (C.2 - A.2))⟩ hC
  have hs1 : 0 < 1 + s := by linarith
  have h1 : 1 / (1 + s) * (1 + s) = 1 := div_mul_cancel₀ _ hs1.ne'
  refine ⟨_, hB, ?_, 1 / (1 + s), div_pos one_pos hs1, ?_, ?_⟩
  · intro h
    apply hAC
    have e1 := congrArg Prod.fst h
    have e2 := congrArg Prod.snd h
    simp only [Dim.pt] at e1 e2
    have k1 : (1 + s) * (C.1 - A.1) = 0 := by linear_combination -e1
    have k2 : (1 + s) * (C.2 - A.2) = 0 := by linear_combination -e2
    apply Prod.ext
    · have h3 := (mul_eq_zero.mp k1).resolve_left hs1.ne'
      linarith
    · have h3 := (mul_eq_zero.mp k2).resolve_left hs1.ne'
      linarith
  · rw [div_lt_one hs1]
    linarith
  · apply Prod.ext
    · simp only [Dim.pt]
      linear_combination (C.1 - A.1) * h1
    · simp only [Dim.pt]
      linear_combination (C.2 - A.2) * h1

end Bound
end HyperbolicPlane
end ParallelPostulate
end
