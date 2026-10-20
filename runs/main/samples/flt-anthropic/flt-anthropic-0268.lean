namespace P2MW.S_Function_orbitCensus_of_dihedralThree_relations

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

namespace P2MKcOrbitCensus

variable {X : Type*} [Fintype X] [DecidableEq X] (a b : X → X)
  (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))

include hb in
theorem b_injective : Function.Injective b := fun x y h => by
  have := congrArg (fun z => b (b z)) h
  simpa [hb] using this

end P2MKcOrbitCensus
end P2MW.S_Function_orbitCensus_of_dihedralThree_relations
