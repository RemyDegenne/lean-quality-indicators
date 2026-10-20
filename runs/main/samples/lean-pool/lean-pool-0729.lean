@[expose] public section

namespace LO

namespace FirstOrder

variable {L : Language}

notation "op(0)" => Zero.zero

notation "op(1)" => One.one

notation "op(+)" => Add.add

notation "op(*)" => Mul.mul

notation "op(=)" => Operator.Eq.eq

notation "op(<)" => Operator.LT.lt

notation "op(≤)" => Operator.LE.le

notation "op(∈)" => Operator.Mem.mem

namespace Rew

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

@[simp] lemma finitary2 (o : Semiterm.Operator L 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω (o.operator ![t₁, t₂]) = o.operator ![ω t₁, ω t₂] := by simp [ω.operator']

end Rew
end FirstOrder
end LO
end
