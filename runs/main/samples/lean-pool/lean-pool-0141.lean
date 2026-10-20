@[expose] public section

namespace MatchingLogic

variable {S : Signature}

namespace Pattern

theorem substVar_eq_self_of_not_mem_allVars {x y : Nat} {p : Pattern S Nat}
    (hx : x ∉ p.allVars) : substVar x y p = p := by
  induction p with
  | var z =>
      simp only [allVars, Finset.mem_singleton] at hx
      simp [substVar, Ne.symm hx]
  | bot => rfl
  | app sigma args ih =>
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
        not_exists] at hx
      simp only [substVar]
      congr
      funext i
      exact ih i (hx i)
  | imp phi psi ihphi ihpsi =>
      simp only [allVars, Finset.mem_union, not_or] at hx
      simp [substVar, ihphi hx.1, ihpsi hx.2]
  | ex z phi ih =>
      simp only [allVars, Finset.mem_insert, not_or] at hx
      simp [substVar, Ne.symm hx.1, ih hx.2]

end Pattern
end MatchingLogic
end
