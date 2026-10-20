@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

namespace PauliExpr

@[simp] lemma eval_one : eval (.one : PauliExpr n) = fun _ => Pauli.I := rfl

end PauliExpr
end QECCertificates
end
