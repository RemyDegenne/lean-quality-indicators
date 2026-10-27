public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

section Step

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F}
  {φ : G → RingAut F} (S : SylowA d W S₁ S₀ W₀ ι κ φ)

include S

namespace SylowA

variable {T : Subgroup G} {δ : G}

theorem φ_one : φ 1 = 1 := by
  have h := S.φ_mul 1 S₁.one_mem 1 S₁.one_mem
  rw [mul_one] at h
  simpa using h

end SylowA
end Step
end CFSG.OddStandard.Seitz77
end
