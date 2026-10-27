public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

section GO

variable {X : Type} [Group X] (V : Type) [Group V] [MulDistribMulAction X V]

variable {V}

namespace GOPair

variable {Y : Subgroup X}

theorem mul_comm' (hGO : GOPair V Y) (a b : V) : a * b = b * a := by
  have h1 : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hGO.exp_two v)
  calc a * b = (a * b)⁻¹ := (h1 _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h1, h1]

end GOPair
end GO
end CFSG.GH74.Uniqueness.SU.SU2
end
