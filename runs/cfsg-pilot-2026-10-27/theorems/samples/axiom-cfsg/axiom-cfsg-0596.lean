public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem a_P_a_inv {p : G} (hp : p ∈ T ⊓ K) : a * p * a⁻¹ ∈ conjugate (T ⊓ K) a := by
  rw [mem_conjugate_iff']
  have e : a * (a * p * a⁻¹) * a⁻¹ = (a * a) * p * (a * a)⁻¹ := by group
  rw [e]
  exact F.core.P_norm _ F.core.a_sq_mem p hp

end Frame
end CFSG.GH74.GLS.Th2.P43f
end
