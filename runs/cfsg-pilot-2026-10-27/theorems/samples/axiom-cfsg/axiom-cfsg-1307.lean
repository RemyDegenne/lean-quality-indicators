public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace CoordSL

section Block

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {s r p : ℕ}
  [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1)

variable {hζ} (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)

include hprim

omit [Finite K] in
theorem torusAct_eq_self_iff {β : Fin s → ZMod p} {x : (Fin s → AdjoinRoot g) × (Fin r → K)} :
    torusAct g (fun i => (β i).val) x = x ↔ ∀ i, β i ≠ 0 → x.1 i = 0 := by
  constructor
  · intro h i hi
    have h1 := congrFun (congrArg Prod.fst h) i
    change AdjoinRoot.root g ^ (β i).val * x.1 i = x.1 i at h1
    have h2 : (AdjoinRoot.root g ^ (β i).val - 1) * x.1 i = 0 := by rw [sub_mul, h1, one_mul,
      sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (root_pow_val_ne_one hprim hi))
  · intro h
    refine Prod.ext (funext fun i => ?_) rfl
    change AdjoinRoot.root g ^ (β i).val * x.1 i = x.1 i
    by_cases hi : β i = 0
    · rw [hi, ZMod.val_zero, pow_zero, one_mul]
    · rw [h i hi, mul_zero]

end Block
end CoordSL
end CFSG.StandardType
end
