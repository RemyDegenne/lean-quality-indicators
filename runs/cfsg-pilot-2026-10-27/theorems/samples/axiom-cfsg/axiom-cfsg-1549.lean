public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ABGLocalTools (IsSylowOf)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem centOverO2_eq_of_pCoreOf_eq_bot {Y L : Subgroup X} (h : CFSG.Open.pCoreOf 2 L = ⊥) :
    F08.CentOverO2 Y L = Y ⊓ centralizer (L : Set X) := by
  unfold F08.CentOverO2
  rw [h]
  have hset : {x : X | x ∈ Y ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ (⊥ : Subgroup X)} =
      (Y ⊓ centralizer (L : Set X) : Set X) := by
    ext x
    constructor
    · rintro ⟨hxY, hx⟩
      refine ⟨hxY, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro l hl
      have hx1 : x * l * x⁻¹ * l⁻¹ = 1 := by
        simpa using hx l hl
      have h1 : x * l * x⁻¹ = l := by
        have := congrArg (· * l) hx1
        simpa [mul_assoc] using this
      have h2 : x * l = l * x := by
        have := congrArg (· * x) h1
        simpa [mul_assoc] using this
      exact h2.symm
    · rintro ⟨hxY, hx⟩
      refine ⟨hxY, fun l hl => ?_⟩
      rw [Subgroup.mem_bot]
      have hxl : l * x = x * l := Subgroup.mem_centralizer_iff.mp hx l hl
      have h2 : x * l = l * x := hxl.symm
      rw [h2]
      simp
  conv_lhs => rw [hset]
  exact Subgroup.closure_eq (Y ⊓ centralizer (L : Set X))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
end
