@[expose] public section

namespace TauCeti

namespace DavisKahan

namespace OperatorIdeal

namespace UnitarilyInvariant

open scoped InnerProductSpace

open Filter Topology MeasureTheory

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace IdealOperator

variable (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]

omit [N.IsComplete] in
@[simp] theorem toOp_sub
    (A B : IdealOperator (E := E) (F := F) N) :
    (A - B).toOp = A.toOp - B.toOp := rfl

end IdealOperator
end
end UnitarilyInvariant
end OperatorIdeal
end DavisKahan
end TauCeti
end
