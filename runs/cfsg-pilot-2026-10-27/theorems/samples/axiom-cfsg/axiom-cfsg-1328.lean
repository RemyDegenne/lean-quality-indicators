public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

universe u

variable {F : Type u} [Field F]

theorem card_torSub [Finite F] (U : Subgroup Fˣ) : Nat.card (torSub F U) = Nat.card U * 2 := by
  let g : U × Bool → torSub F U := fun x => ⟨tor F x.1 * swp F x.2, x.1, x.1.2, x.2, rfl⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨y, ε⟩ ⟨y', ε'⟩ h
      obtain ⟨h1, h2⟩ := tor_mul_swp_injective (congrArg Subtype.val h)
      simp only at h1 h2
      rw [Subtype.ext h1, h2]
    · rintro ⟨_, y, hy, ε, rfl⟩
      exact ⟨⟨⟨y, hy⟩, ε⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective g hg), Nat.card_prod, show Nat.card Bool = 2 by simp]

end CFSG.ComponentClassification.AutL2Facts
end
