namespace OAI

noncomputable section

open scoped BigOperators

namespace Contingency.BitModel.StackCode

@[simp] theorem compile_second (P : Program) (pc : Fin P.labels) (coin : Bool) (heads) :
    (compile P).transition (second pc) coin heads=execute P pc coin heads := by
  simp [compile,second]

end Contingency.BitModel.StackCode
end
end OAI
