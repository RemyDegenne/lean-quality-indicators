public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

namespace Decomp

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (D : Decomp S)

section Five

variable (hB : ∀ h : G, h * S.z * h⁻¹ ∈ D.B → h * S.z * h⁻¹ = S.z) (h8 : 8 < Nat.card D.A)
  (hB8 : 8 < Nat.card D.B ∨ ∀ b ∈ D.B, b ^ 2 = 1 → b = 1 ∨ b = S.z)

omit hB h8 in
include hB8 in
theorem conj_hB8 (g : G) : 8 < Nat.card (D.conj g).B ∨
    ∀ b ∈ (D.conj g).B, b ^ 2 = 1 → b = 1 ∨ b = (S.conjBy g).z := by
  rcases hB8 with h' | h'
  · left
    rw [D.card_conj_B]
    exact h'
  · right
    intro b hb hb2
    rw [D.mem_conj_B] at hb
    have hb2' : (g⁻¹ * b * g) ^ 2 = 1 := by
      rw [show g⁻¹ * b * g = g⁻¹ * b * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hb2]
      group
    rcases h' _ hb hb2' with e | e
    · left
      calc b = g * (g⁻¹ * b * g) * g⁻¹ := by group
        _ = 1 := by rw [e]; group
    · right
      rw [Setting.conjBy_z]
      calc b = g * (g⁻¹ * b * g) * g⁻¹ := by group
        _ = g * S.z * g⁻¹ := by rw [e]

end Five
end Decomp
end Sm77
end CFSG.LargeExtraspecial.DW
end
