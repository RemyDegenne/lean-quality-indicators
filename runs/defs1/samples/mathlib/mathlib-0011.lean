@[expose] public section

open Set

variable {ι ι' R : Type*} [Ring R] (I J : Ideal R) {a b : R}

namespace Ideal

variable {I} {x y : R}

variable [I.IsTwoSided]

variable (I)

section Pi

variable (ι) in
/-- `R^n/I^n` is isomorphic to `(R/I)^n` as an `R/I`-module. -/
noncomputable def piQuotEquiv [I.IsTwoSided] : ((ι → R) ⧸ pi fun _ ↦ I) ≃ₗ[R ⧸ I] ι → (R ⧸ I) where
  toFun x := Quotient.liftOn' x (fun f i ↦ Ideal.Quotient.mk I (f i)) fun _ _ hab ↦
    funext fun i ↦ (Submodule.Quotient.eq' _).2 (QuotientAddGroup.leftRel_apply.mp hab i)
  map_add' := by rintro ⟨_⟩ ⟨_⟩; rfl
  map_smul' := by rintro ⟨_⟩ ⟨_⟩; rfl
  invFun x := Ideal.Quotient.mk _ (Quotient.out <| x ·)
  left_inv := by
    rintro ⟨x⟩
    exact Ideal.Quotient.eq.2 fun i ↦ Ideal.Quotient.eq.1 (Quotient.out_eq' _)
  right_inv x := funext fun i ↦ Quotient.out_eq' (x i)

end Pi
end Ideal
end
