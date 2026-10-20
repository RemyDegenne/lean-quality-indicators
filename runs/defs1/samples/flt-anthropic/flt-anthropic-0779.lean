set_option autoImplicit false

noncomputable section

namespace ModularCurve.IgusaCover

open AlgebraicCurve

variable {κ : Type*} [Field κ] {Ω : Type*} [Field Ω] [Algebra κ Ω]

variable (K₀ : IntermediateField κ Ω) (a : Ω)

structure IsKummerGenerator (n : ℕ) (K₀ : IntermediateField κ Ω) (a : Ω) : Prop where

  pos : 0 < n
  ne_zero : a ≠ 0
  pow_mem : a ^ n ∈ K₀

end ModularCurve.IgusaCover
end
