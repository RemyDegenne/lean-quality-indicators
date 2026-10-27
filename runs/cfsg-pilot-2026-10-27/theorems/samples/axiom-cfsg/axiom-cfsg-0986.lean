public section

namespace CFSG.Quasithin.A312M23

open CFSG.Quasithin.A312Words

open scoped commutatorElement

variable {Γ α : Type} [Group Γ] [MulAction Γ α] {m : ℕ}

theorem closure_fix {vl : List Γ} {pt : Fin m → α} (hvfix : ∀ a ∈ vl, ∀ i, a • pt i = pt i) :
    ∀ v ∈ Subgroup.closure {x | x ∈ vl}, ∀ i, v • pt i = pt i := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem x hx => exact hvfix x hx
  | one => intro i; exact one_smul _ _
  | mul x y _ _ ihx ihy => intro i; rw [mul_smul, ihy, ihx]
  | inv x _ ihx => intro i; exact inv_smul_eq_iff.mpr (ihx i).symm

end CFSG.Quasithin.A312M23
end
