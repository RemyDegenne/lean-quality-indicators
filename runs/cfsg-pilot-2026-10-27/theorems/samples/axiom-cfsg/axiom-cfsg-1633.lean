public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h}

theorem x'_eq_x_mul_v (h : IsAConfig 5 x K T Q S a) : a * x * a⁻¹ = x * L4.vElt x a :=
  (L4.x_mul_v h).symm

end CFSG.GH74.GLS.C3.Layer2.L5
end
