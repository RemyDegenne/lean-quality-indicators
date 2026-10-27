@[expose] public section

universe u v

namespace WType

section Nat

open Sum PUnit

/-- `WType.Natα` is equivalent to `PUnit ⊕ PUnit`.
This is useful when considering the associated polynomial endofunctor.
-/
@[simps]
def NatαEquivPUnitSumPUnit : Natα ≃ PUnit.{u + 1} ⊕ PUnit where
  toFun c :=
    match c with
    | Natα.zero => inl unit
    | Natα.succ => inr unit
  invFun b :=
    match b with
    | inl _ => Natα.zero
    | inr _ => Natα.succ
  left_inv c :=
    match c with
    | Natα.zero => rfl
    | Natα.succ => rfl
  right_inv b :=
    match b with
    | inl _ => rfl
    | inr _ => rfl

end Nat
end WType
end
