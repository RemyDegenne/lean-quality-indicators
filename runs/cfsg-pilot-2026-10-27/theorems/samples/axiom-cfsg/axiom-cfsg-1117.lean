public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3CH

open scoped MatrixGroups

section Parity

variable {G : Type} [Group G]

theorem exists_mul_centralizes_of_odd [Finite G] {s : G} (hs2 : s * s = 1) {O : Subgroup G}
    (hO : Odd (Nat.card O)) (hsO : ∀ o ∈ O, s * o * s⁻¹ ∈ O) {y : G}
    (hy : y⁻¹ * (s * y * s⁻¹) ∈ O) : ∃ o ∈ O, s * (y * o) * s⁻¹ = y * o := by
  set u : G := y⁻¹ * (s * y * s⁻¹) with hu
  have hss : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hs2, inv_one]
  have key : s * u * s⁻¹ = (s * y * s⁻¹)⁻¹ * y := by
    calc s * u * s⁻¹ = (s * y⁻¹ * s⁻¹) * ((s * s) * y * (s⁻¹ * s⁻¹)) := by rw [hu]; group
      _ = (s * y * s⁻¹)⁻¹ * y := by rw [hs2, hss]; group
  have h1 : u * (s * u * s⁻¹) = 1 := by rw [key, hu]; group
  let φ : O → O := fun o => ⟨u * (s * o * s⁻¹), O.mul_mem hy (hsO o o.2)⟩
  have hφ : Function.Involutive φ := by
    intro o
    apply Subtype.ext
    show u * (s * (u * (s * (o : G) * s⁻¹)) * s⁻¹) = o
    calc u * (s * (u * (s * (o : G) * s⁻¹)) * s⁻¹)
        = (u * (s * u * s⁻¹)) * ((s * s) * (o : G) * (s⁻¹ * s⁻¹)) := by group
      _ = o := by rw [h1, hs2, hss]; group
  obtain ⟨o, ho⟩ := exists_fixed_of_involutive_odd φ hφ hO
  refine ⟨o, o.2, ?_⟩
  have h2 : u * (s * (o : G) * s⁻¹) = o := congrArg Subtype.val ho
  calc s * (y * o) * s⁻¹ = (s * y * s⁻¹) * (s * o * s⁻¹) := by group
    _ = y * (u * (s * o * s⁻¹)) := by rw [hu]; group
    _ = y * o := by rw [h2]

end Parity
end CFSG.ClassicalInvolution.Q3.Q3AM
end
