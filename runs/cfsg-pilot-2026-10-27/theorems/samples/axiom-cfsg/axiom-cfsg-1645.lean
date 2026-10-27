namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open Polynomial

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Algebra (ZMod p) F]

variable {f : (ZMod p)[X]}

theorem irreducible_of_natDegree_eq_three (hdeg : f.natDegree = 3)
    (hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c) : Irreducible f :=
  irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) hnoroot

end
end CFSG.FeitThompson
